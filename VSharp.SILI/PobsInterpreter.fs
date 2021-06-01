namespace VSharp.Interpreter.IL

open System
open System.Collections.Generic
open System.Reflection
open System.Reflection.Emit
open System.Text
open FSharpx.Collections

open VSharp
open VSharp.Core
open ipOperations
open CilStateOperations
open Instruction

type public PobsInterpreter(searcher : INewSearcher) =
    inherit ExplorerBase()
    let infty = System.Int32.MaxValue
    let GlobalBound = 200
    let initialOpStackSize = 0u
    let qFront = List<cilState>()
    let qBack = List<pob * cilState>()
    let transition = Dictionary<ip, cilState list>()
    let witnesses = Dictionary<pob, cilState list>()
    let blockedLocs = Dictionary<pob, ip list>()
    let possiblePobsLocs = List<ip>()
    let sPobs = Dictionary<cilState, pob list>()
    let mutable curLvl = searcher.MaxBound
    let mainPobs = List<pob>()
    let currentPobs = List<pob>()
    let answeredPobs = Dictionary<pob, pobStatus>()
    let parents = Dictionary<pob, pob>()
    let canReach state (loc : ip) (blockedLocs : ip list) =
        //TODO: use CFG-reachability analysis
        searcher.CanReach (state, loc, blockedLocs)
    let addToDictionaryWithListValue (d : Dictionary<'a, 'b list>) k elem =
        let v = d.GetValueOrDefault(k, [])
        d.[k] <- (elem :: v)

    let removeFromDictionaryWithListValue (d : Dictionary<'a, 'b list>) k elem =
        let v = d.GetValueOrDefault(k, [])
        let v' = List.filter (fun x -> x <> elem) v
        d.[k] <- v'

    let removeFromGlobalVars (s : cilState, p : pob) =
        removeFromDictionaryWithListValue sPobs s p
        removeFromDictionaryWithListValue witnesses p s

    let addWitness(s : cilState, p : pob) =
        let sLvl = levelToInt s.level
        try
            if sLvl <= p.lvl && canReach s.ipStack p.loc blockedLocs.[p] then
                addToDictionaryWithListValue witnesses p s
                addToDictionaryWithListValue sPobs s p
            else
                let res = sLvl <= p.lvl
                let res2 = canReach s.ipStack p.loc blockedLocs.[p]
                Logger.info "state with ipStack = %O is not witnessing pob = %O" s.ipStack p
                Logger.info "state.Lvl <= p.lvl = %O" res
                Logger.info "canReach = %O" res2
        with
        | :? KeyNotFoundException -> __notImplemented__()
    let rec blockWitness(s', p') =
        removeFromGlobalVars(s', p')
        match List.exists (fun (s : cilState) -> s.startingIP = s'.startingIP) witnesses.[p'] with
        | true -> ()
        | false ->
            addToDictionaryWithListValue blockedLocs p' s'.startingIP
            List.iter (fun (s : cilState) ->
                if not <| canReach s.ipStack p'.loc blockedLocs.[p'] then blockWitness(s, p')) witnesses.[p']

    let addPob(parent : pob, child : pob) =
        assert(parents.ContainsKey(child) |> not)
        parents.Add(child, parent)
        currentPobs.Add child
        blockedLocs.Add(child, [])
        Seq.iter (fun s -> addWitness(s, child)) qFront
        Seq.iter (fun s -> qBack.Add(child, s)) transition.[child.loc]

    let rec answerYes (s' : cilState, p' : pob) =
        if Seq.contains p' mainPobs then mainPobs.Remove(p') |> ignore
        if answeredPobs.ContainsKey p' |> not then answeredPobs.Add(p', Witnessed s')
        else answeredPobs.[p'] <- Witnessed s'
        removeFromGlobalVars(s', p')
        if parents.ContainsKey p' then answerYes(s', parents.[p'])

    member x.MakeCilStateForIp (ip : ip) =
        let m = methodOf ip
        let cilStates = x.FormInitialState (x.MakeMethodIdentifier m)
        match cilStates with
        | [cilState] -> {cilState with startingIP = ip} |> withIpStack [ip]
        | _ -> __notImplemented__()

    //NOTE: Must be called for ip with empty evaluation stack!
    member x.Start (loc : ip) =
        possiblePobsLocs.Add(loc)
        let start = x.MakeCilStateForIp loc
        qFront.Add(start)
        searcher.AppendNewStates [start] |> ignore
        Seq.iter (fun p -> addWitness(start, p)) currentPobs

    member x.Forward (s : cilState) =
        assert(sPobs.ContainsKey s)
        match sPobs.[s] with
        | [] -> ()
        | _ -> ()
        let removed = qFront.Remove(s) in assert(removed)
        let goodStates, incompleteStates, errors = ILInterpreter(x).ExecuteOnlyOneInstruction s
        qFront.AddRange (goodStates @ incompleteStates @ errors)
        searcher.AppendNewStates(goodStates)
        goodStates |> List.iter (fun (s' : cilState) ->
            match currentIp s' with
            | Instruction(0x64, _) -> ()
            | _ -> ()
            if not <| sPobs.ContainsKey(s') then sPobs.Add(s', [])
            let ip' = currentIp s'
            if Seq.contains ip' possiblePobsLocs then addToDictionaryWithListValue transition ip' s'
            sPobs.[s] |> List.iter (fun p ->
                addWitness(s', p)
                assert(sPobs.ContainsKey s')
                if p.loc = currentIp s' then qBack.Add(p, s')                )
        )
        List.iter (fun (p : pob) -> if p.loc <> currentIp s then removeFromGlobalVars(s, p)) sPobs.[s]

    member x.OverApproximate(_ : ip, _ : int) : term = Terms.True

    member x.Backward (p' : pob, s' : cilState, EP : ip) =
        let removed = qBack.Remove(p',s') in assert(removed)
        assert(currentIp s' = p'.loc)
        let lvl = p'.lvl - (levelToInt s'.level)
        let fml = Memory.WLP s'.state p'.fml
        match Memory.IsSAT fml with
        | true when s'.startingIP = EP ->
            let removed = currentPobs.Remove(p') in assert(removed)
            let removed = witnesses.Remove(p') in assert(removed)
            let removed = blockedLocs.Remove(p') in assert(removed)
            qBack.RemoveAll(fun (p, _) -> p = p') |> ignore
            answerYes(s', p')
        | true ->
            let p = {loc = s'.startingIP; lvl = lvl; fml = fml}
            addPob(p', p)
        | false ->
            Logger.info "UNSAT for pob = %O and s' = %O" p' s'
    member x.PropDirSymExec (mainId : IFunctionIdentifier) (EP : ip) mainPobsList =
        List.iter (fun p -> mainPobs.Add p) mainPobsList
        let createPobs () =
            mainPobs |> Seq.iter (fun (mp : pob) ->
                let p = {mp with lvl = curLvl}
                blockedLocs.Add(p, [])
                witnesses.Add(p, [])
                parents.Add(p, mp)
                currentPobs.Add p)
        while mainPobs.Count > 0 && curLvl <= searcher.MaxBound do
            createPobs()
            while currentPobs.Count > 0 do
                match searcher.ChooseAction(List.ofSeq qFront, List.ofSeq qBack, List.ofSeq currentPobs, mainId) with
                | Stop -> currentPobs.Clear()
                | Start loc -> x.Start(loc)
                | GoForward s ->
                    match currentIp s with
                    | Instruction(0x64, _) -> ()
                    | _ -> ()
                    Logger.info "GoForward: ip = %O" (currentIp s)
                    x.Forward(s)
                | GoBackward(p', s') -> x.Backward(p',s', EP)
            curLvl <- curLvl + 1
    member x.ClearStructures () =
        curLvl <- searcher.MaxBound
        mainPobs.Clear()
        qFront.Clear()
        qBack.Clear()
        transition.Clear()
        witnesses.Clear()
        blockedLocs.Clear()
        possiblePobsLocs.Clear()
        sPobs.Clear()
        mainPobs.Clear()
        currentPobs.Clear()
        answeredPobs.Clear()
        parents.Clear()
        searcher.Reset()
    override x.Invoke _ _ _ = __notImplemented__()
    override x.AnswerPobs entryMethodId codeLocations k =
        let printLocInfo (loc : codeLocation) =
            Logger.info "Got loc {%O, %O}" loc.offset loc.method
        List.iter printLocInfo codeLocations

        x.ClearStructures()
        let mainPobs =
            codeLocations
            |> List.filter (fun loc -> loc.method.GetMethodBody().GetILAsByteArray().Length > loc.offset)
            |> List.map (fun (loc : codeLocation) -> {loc = Instruction(loc.offset, loc.method); lvl = infty; fml = Terms.True})
        List.iter (fun p -> answeredPobs.Add(p, Unknown)) mainPobs
        let EP = Instruction(0, entryMethodId.Method)
        x.PropDirSymExec entryMethodId EP mainPobs
        let showResultFor (mp : pob) =
            match answeredPobs.[mp] with
            | Unreachable -> Logger.info "NO: MainPob = %O" mp
            | Witnessed s -> Logger.info "YES: MainPob = %O, witness = %O" mp s
            | Unknown -> Logger.info "Unknown: MainPoob = %O" mp
        List.iter showResultFor mainPobs
        let addLocationStatus (acc : Dictionary<codeLocation, string>) (loc : codeLocation) =
            let pob = {loc = Instruction(loc.offset, loc.method); lvl = infty; fml = Terms.True}
            let result =
                match answeredPobs.[pob] with
                | Witnessed _ -> "Witnessed"
                | status -> status.ToString()
            acc.Add(loc, result)
            acc
        let result = codeLocations |> Seq.fold addLocationStatus (new Dictionary<codeLocation, string>())
        k result

    override x.MakeMethodIdentifier m = { methodBase = m } :> IMethodIdentifier

 [<CustomComparison; CustomEquality>]
 type reachabilityEvaluation =
    | Unknown
    | Reachable of int * int  // cost to go to target and cost to go to exit
    with
    override x.Equals y =
        match y with
        | :? reachabilityEvaluation as y ->
            match x, y with
            | Unknown, Unknown -> true
            | Reachable(p1, p2), Reachable(p3, p4) -> p1 = p2 && p3 = p4
            | _ -> false
        | _ -> false
    override x.GetHashCode() = x.ToString().GetHashCode()
    interface IComparable with
        override x.CompareTo y =
            match y with
            | :? reachabilityEvaluation as r ->
                match x, r with
                | Unknown, Unknown -> 0
                | Unknown, Reachable _ -> 1
                | Reachable _, Unknown _ -> -1
                | Reachable(p1, p2), Reachable(p3, p4) when p1 < p3 || p1 = p3 && p2 < p4 -> -1
                | Reachable(p1, p2), Reachable(p3, p4) when p1 = p3 && p2 = p4 -> 0
                | _ -> 1
            | _ -> -1

type cilstatesComparer(target, reachableLocations : Dictionary<codeLocation, codeLocation list>, reachableMethods : Dictionary<codeLocation, MethodBase list>,
                       methodsReachabilityTransitiveClosure : Dictionary<MethodBase, MethodBase list>) =
    let COST_OF_MANY_CALLS = 3000
    let COST_OF_CALL = 500
    let COST_OF_EXIT = 100
    let REGULAR_COST = 20
    let COST_TO_GO_TO_ENDFINALLY = 50
    let UNKNOWN_CONSTANT = Int32.MaxValue

    let ip2codeLocation (ip : ip) =
        match offsetOf ip, methodOf ip with
        | None, _ -> None
        | Some offset, m ->
            let loc = {offset = offset; method = m}
            Some loc
    let min(x, y) = if x < y then x else y

    let loc2Locs (loc : codeLocation) =
        match reachableLocations.ContainsKey loc with
        | true -> reachableLocations.[loc]
        | _ -> []

    let loc2Methods (loc : codeLocation) =
        match reachableMethods.ContainsKey loc with
        | true -> reachableMethods.[loc]
        | _ -> []

    let method2Methods (m : MethodBase) =
        match methodsReachabilityTransitiveClosure.ContainsKey m with
        | true -> methodsReachabilityTransitiveClosure.[m]
        | _ -> []

    let canReachMetrics(ipStack : ip list, _ : ip list) : reachabilityEvaluation =
        let helper target acc ip =
            let currentReachableCost, currentCostToExit =
                match acc with
                | Reachable(x, y) -> x, y
                | Unknown -> UNKNOWN_CONSTANT, 0
            let findNewCost price =
                Reachable(min(currentReachableCost, currentCostToExit + price), currentCostToExit + COST_OF_EXIT)
            match ip2codeLocation ip with
            | Some loc when not <| reachableLocations.ContainsKey(loc) -> findNewCost COST_TO_GO_TO_ENDFINALLY
            | Some loc when List.contains target (loc2Locs loc) -> findNewCost REGULAR_COST
            | Some loc when List.contains target.method (loc2Methods loc) -> findNewCost COST_OF_CALL
            | Some loc when Seq.exists (fun m -> List.contains target.method (method2Methods m)) (loc2Methods loc) ->
                findNewCost COST_OF_MANY_CALLS
            | _  -> Reachable(currentReachableCost, currentCostToExit + COST_OF_EXIT)
        match ip2codeLocation target with
        | None -> Unknown
        | Some target -> List.fold (helper target) Unknown ipStack

//    member x.Append (s : cilState) =
//        if x.CanReach (s.ipStack, []) then
    member x.CanReach(ipStack, blocked) =
        match canReachMetrics(ipStack, blocked) with
        | Unknown -> __unreachable__()
        | Reachable(x, _) -> x <> UNKNOWN_CONSTANT

    interface IComparer<cilState> with
        override x.Compare (a : cilState, b : cilState) =
            let aCanReach = canReachMetrics(a.ipStack, [])
            let bCanReach = canReachMetrics(b.ipStack, [])
            match aCanReach, bCanReach with
            | Reachable(x, _), Reachable(y, _) when x < y -> -1
            | Reachable(x, _), Reachable(y, _) when x = y -> 0
            | Reachable(x, _), Reachable(y, _)  -> 1
            | _ -> __unreachable__()


type TargetedSearcher(maxBound) =

    let reachableLocations = Dictionary<codeLocation, codeLocation list>()
    let reachableMethods = Dictionary<codeLocation, MethodBase list>()
    let methodsReachability = Dictionary<MethodBase, MethodBase list>()
    let methodsReachabilityTransitiveClosure = Dictionary<MethodBase, MethodBase list>()
    let mutable target = Exit null
    let mutable comparer = cilstatesComparer(target, null, null, null)
    let mutable priorityQueue = null

    let mutable entryMethod : MethodBase = null
    let appendReachableInfo (cfg : cfg) (reachableLocsForSCC : HashSet<codeLocation>) (reachableMethodsForSCC : HashSet<MethodBase>) (current : offset) =
        let currentLoc = {offset = current; method = cfg.methodBase}
        reachableLocsForSCC.Add(currentLoc) |> ignore
        if cfg.offsetsDemandingCall.ContainsKey current then
           let _, calledMethod = cfg.offsetsDemandingCall.[current]
           if calledMethod.DeclaringType.Assembly = entryMethod.DeclaringType.Assembly then
            reachableMethodsForSCC.Add(calledMethod) |> ignore

        let helper (target : offset) =
            let loc = {offset = target; method = cfg.methodBase}
            if not <| reachableLocations.ContainsKey loc then ()
            List.iter (reachableLocsForSCC.Add >> ignore) reachableLocations.[loc]
            List.iter (reachableMethodsForSCC.Add >> ignore) reachableMethods.[loc]
        let targets = cfg.graph.[current]
        Seq.iter helper targets

    let commitReachableInfo (cfg : cfg) (reachableLocsForSCC : HashSet<codeLocation>) (reachableMethodsForSCC : HashSet<MethodBase>) (current : offset) =
        let currentLoc = {offset = current; method = cfg.methodBase}
        reachableLocations.[currentLoc] <-  List.ofSeq (reachableLocsForSCC)
        reachableMethods.[currentLoc] <- List.ofSeq (reachableMethodsForSCC)

    let initReachableInfo (cfg : cfg) (current : offset) =
        let currentLoc = {offset = current; method = cfg.methodBase}
        reachableLocations.Add(currentLoc, [])
        reachableMethods.Add(currentLoc, [])
    let buildReachabilityInfo (currentMethod : MethodBase) : MethodBase list =
        let cfg = CFG.build currentMethod

        let rec dfsSCC (usedSCC : int list) (v : offset) : int list =
            let currentSCC = cfg.sccOut.[v]
            if List.contains currentSCC usedSCC then usedSCC
            else
                let usedSCC = currentSCC :: usedSCC
                let currentSCCOffsets = Seq.filter (fun offset -> currentSCC = cfg.sccOut.[offset]) cfg.sortedOffsets
                let newUsed = Seq.fold (fun acc u1 -> Seq.fold (fun acc u2 -> dfsSCC acc u2) acc cfg.graph.[u1]) usedSCC currentSCCOffsets
                let reachableLocsForSCC = HashSet<codeLocation>()
                let reachableMethodsForSCC = HashSet<MethodBase>()
                Seq.iter (initReachableInfo cfg) currentSCCOffsets
                Seq.iter (appendReachableInfo cfg reachableLocsForSCC reachableMethodsForSCC) currentSCCOffsets
                Seq.iter (commitReachableInfo cfg reachableLocsForSCC reachableMethodsForSCC) currentSCCOffsets
                newUsed
        let _ = dfsSCC [] 0 //TODO: what about EHC?
        reachableMethods.[{offset = 0; method = currentMethod}]

    let addCall (current : MethodBase) (calledMethods : MethodBase list) =
        let add m (ms : MethodBase list) (d : Dictionary<_, MethodBase list >) =
            if d.ContainsKey m then d.[m] <- ms @ d.[m]
            else d.Add(m, ms)

        add current calledMethods methodsReachability

    let buildReachability () =
        let rec exit processedMethods = function
                | [] -> ()
                | m :: q' -> findFixPoint (processedMethods, q') m
        and findFixPoint (processedMethods : MethodBase list, methodsQueue : MethodBase list) (current : MethodBase) =
            if List.contains current processedMethods then exit processedMethods methodsQueue
            else
                let processedMethods = current :: processedMethods
                let calledMethods = buildReachabilityInfo current
                addCall current calledMethods

                exit processedMethods (methodsQueue @ calledMethods)
        findFixPoint ([],[]) entryMethod

    let makeTransitiveClosure () =
        let findReachableMethodsForMethod (current : MethodBase) =
            Logger.info "Iterating for %O" current
            methodsReachabilityTransitiveClosure.Add(current, [])
            let used = HashSet<MethodBase>()
            let rec dfs (v : MethodBase) =
                if used.Contains v then ()
                else
                    used.Add(v) |> ignore
                    methodsReachabilityTransitiveClosure.[current] <- v :: methodsReachability.[current]
                    List.iter dfs (methodsReachability.[v])
            List.iter dfs methodsReachability.[current]
        Seq.iter findReachableMethodsForMethod (methodsReachability.Keys)
    let print () =
        Logger.info "Calculated CFG Reachability\n"
        methodsReachabilityTransitiveClosure |> Seq.iter (fun kvp ->
            let value = List.fold (fun (sb : StringBuilder) m -> sb.AppendFormat("{0}; ", m.ToString())) (StringBuilder()) kvp.Value
            Logger.info "key = %O; Value = %s" kvp.Key (value.ToString()))

    let init main t =
        target <- t
        entryMethod <- main
        buildReachability ()
        makeTransitiveClosure ()
        comparer <- cilstatesComparer(target, reachableLocations, reachableMethods, methodsReachabilityTransitiveClosure)
        priorityQueue <- C5.IntervalHeap<cilState>(comparer)
        print ()

    interface INewSearcher with
        override x.CanReach(ipStack : ip list, target : ip, blocked : ip list) = comparer.CanReach(ipStack, blocked)
        override x.MaxBound = maxBound
        override x.AppendNewStates states =
            List.iter (fun s -> if comparer.CanReach(s.ipStack, []) then priorityQueue.Add s |> ignore) states

        override x.Reset() =
            reachableLocations.Clear()
            reachableMethods.Clear()
            methodsReachability.Clear()
            methodsReachabilityTransitiveClosure.Clear()
            entryMethod <- null
        override x.ChooseAction(qf,qb,pobs,mainId) =
            let t =
                match pobs with
                | [] -> Exit null
                | p :: _ -> p.loc

            if entryMethod = null then
                init mainId.Method t
            let tryFindState acc (p : pob) =
                match acc with
                | Some _ -> acc
                | _ ->
//                    let sorted =
//                        qf |> List.filter (fun s -> levelToInt s.level <= maxBound)
//                        |> List.sortBy (fun (s : cilState) -> canReachMetrics(s.ipStack, p.loc, []))
                    match priorityQueue.IsEmpty with
                    | true -> None
                    | _ ->
                        let s = priorityQueue.FindMin()
                        priorityQueue.DeleteMin() |> ignore
                        Some s

            match qf, qb, pobs with
            | [], _, _ -> Start(Instruction(0, mainId.Method))
            | _, b ::_, _ -> GoBackward(b)
            | _, _, [] -> Stop
            | _, _, pobs ->
                let s = List.fold tryFindState None pobs
                match s with
                | None -> Stop
                | Some s -> GoForward s
