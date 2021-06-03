namespace VSharp.Interpreter.IL

open System
open System.Collections.Generic
open System.Reflection
open System.Reflection.Emit
open System.Text
open C5
open FSharpx.Collections
open FSharpx.Collections
open FSharpx.Collections
open InstructionsSet
open CilStateOperations
open VSharp
open VSharp
open VSharp.Core
open ipOperations
open Instruction

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

module MyUtils =
    let ip2codeLocation (ip : ip) =
        match offsetOf ip, methodOf ip with
        | None, _ -> None
        | Some offset, m ->
            let loc = {offset = offset; method = m}
            Some loc

type cilstatesComparer(target : codeLocation, cfg : cfg, reachableLocations : Dictionary<codeLocation, codeLocation HashSet>, reachableMethods : Dictionary<codeLocation, MethodBase HashSet>,
                       methodsReachabilityTransitiveClosure : Dictionary<MethodBase, MethodBase HashSet>) =
    let COST_OF_MANY_CALLS = 3000
    let COST_OF_CALL = 100
    let COST_OF_EXIT = 50
    let REGULAR_COST = 20
    let COST_TO_GO_TO_ENDFINALLY = 50
    let UNKNOWN_CONSTANT = Int32.MaxValue
//    let


    let min(x, y) = if x < y then x else y

    let loc2Locs (loc : codeLocation) =
        match reachableLocations.ContainsKey loc with
        | true -> reachableLocations.[loc]
        | _ -> HashSet()

    let loc2Methods (loc : codeLocation) =
        match reachableMethods.ContainsKey loc with
        | true -> reachableMethods.[loc]
        | _ -> HashSet()

    let method2Methods (m : MethodBase) =
        match methodsReachabilityTransitiveClosure.ContainsKey m with
        | true -> methodsReachabilityTransitiveClosure.[m]
        | _ -> HashSet()

    let canReachMetrics3 (ip : ip) : reachabilityEvaluation =
       match MyUtils.ip2codeLocation ip with
       | Some l when Seq.contains target (loc2Locs l) -> Reachable(20, 0)
//            let u = l.offset
//            let v = target.offset
//            let dist = CFG.findDistance cfg

       | _ -> Reachable(UNKNOWN_CONSTANT, 0)

    let canReachMetrics2 (ip : ip) : reachabilityEvaluation =
       match MyUtils.ip2codeLocation ip with
       | Some l when Seq.contains target (loc2Locs l) ->
            let u = l.offset
            let v = target.offset
            let dist = CFG.findDistance cfg
            Reachable(dist.[u,v], 0)
       | _ -> Reachable(UNKNOWN_CONSTANT, 0)
    let canReachMetrics(ipStack : ip list) : reachabilityEvaluation =
        let helper target acc ip =
            let currentReachableCost, currentCostToExit =
                match acc with
                | Reachable(x, y) -> x, y
                | Unknown -> UNKNOWN_CONSTANT, 0
            let findNewCost price =
                Reachable(min(currentReachableCost, currentCostToExit + price), currentCostToExit + COST_OF_EXIT)
            match MyUtils.ip2codeLocation ip with
            | Some loc when not <| reachableLocations.ContainsKey(loc) -> findNewCost COST_TO_GO_TO_ENDFINALLY
            | Some loc when Seq.contains target (loc2Locs loc) ->
                let u = loc.offset
                let v = target.offset
                let dist = CFG.findDistance cfg
                if dist.ContainsKey (u,v) |> not then
                    Logger.warning "FLOYDs DISTANCE is wrong!"
                    Seq.iter (Logger.warning "%d -> %d" u) cfg.graph.[u]
                    ()

                let price = dist.[u,v]
//                Logger.warning "FLOYDs DISTANCE from (%s, %s) = %d" (u.ToString("X4")) (v.ToString("X4")) price
                findNewCost price
//            | Some loc when Seq.contains target.method (loc2Methods loc) -> findNewCost COST_OF_CALL
//            | Some loc when Seq.exists (fun m -> Seq.contains target.method (method2Methods m)) (loc2Methods loc) ->
//                findNewCost COST_OF_MANY_CALLS
            | _  -> Reachable(currentReachableCost, currentCostToExit + COST_OF_EXIT)
        List.fold (helper target) Unknown ipStack

//    member x.Append (s : cilState) =
//        if x.CanReach (s.ipStack, []) then
    member x.CanReach(ipStack, blocked) = true
//        match canReachMetrics(ipStack, blocked) with
//        | Unknown -> __unreachable__()
//        | Reachable(x, _) -> x <> UNKNOWN_CONSTANT

    interface IComparer<cilState> with
        override x.Compare (a : cilState, b : cilState) =
//            if a.stepsNumber > 1000u then 1 else
            let aCanReach = canReachMetrics(a.ipStack)
            let bCanReach = canReachMetrics(b.ipStack)
            match aCanReach, bCanReach with
            | Reachable(x, _), Reachable(y, _) when x < y -> -1
            | Reachable(x, _), Reachable(y, _) when x = y -> 0
//                if a.stepsNumber < b.stepsNumber then -1
//                elif a.stepsNumber = b.stepsNumber then 0
//                else 1
            | Reachable(x, _), Reachable(y, _)  -> 1
            | _ -> __unreachable__()

type OneTargetedSearcher(maxBound, target : codeLocation, cfg, reachableLocations, reachableMethods, methodsReachabilityTransitiveClosure ) =
    let comparer = cilstatesComparer(target, cfg, reachableLocations, reachableMethods, methodsReachabilityTransitiveClosure)
    let priorityQueue  = C5.IntervalHeap<cilState>(comparer)
    let mutable stepsNumber = 0u

    member x.GetNext() =
        match priorityQueue.IsEmpty with
        | true -> None
        | _ ->
            let s = priorityQueue.FindMin()
            priorityQueue.DeleteMin() |> ignore
            Some s

    interface INewSearcher with
        override x.CanReach(ipStack : ip list, target : ip, blocked : ip list) = comparer.CanReach(ipStack, blocked)
        override x.MaxBound = maxBound
        override x.AppendNewStates states =
//            List.iter (fun s -> if comparer.CanReach(s.ipStack, []) then priorityQueue.Add s |> ignore) states
            Seq.iter (fun s -> priorityQueue.Add s |> ignore) states
        override x.Reset() =
            Logger.warning "steps number done by %O = %d" (x.GetType()) stepsNumber
            stepsNumber <- 0u
        override x.Init(_,_) = ()
        override x.ChooseAction(_,_,_,_) =
            __notImplemented__()

type TargetedSearcher(maxBound) =
    let reachableLocations = Dictionary<codeLocation, HashSet<codeLocation>>()
    let reachableMethods = Dictionary<codeLocation, HashSet<MethodBase>>()
    let methodsReachability = Dictionary<MethodBase, HashSet<MethodBase>>()
    let methodsReachabilityTransitiveClosure = Dictionary<MethodBase, HashSet<MethodBase>>()

    let noLoc = {offset = 0; method = null}
    let mutable entryMethod : MethodBase = null
    let mutable stepsNumber = 0u
    let mutable currentLoc = noLoc
    let mutable currentSearcher : OneTargetedSearcher option = None
//    let searchers = List<OneTargetedSearcher>()
//    let loc2Searcher = Dictionary<codeLocation, OneTargetedSearcher>()
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
            Seq.iter (reachableLocsForSCC.Add >> ignore) reachableLocations.[loc]
            Seq.iter (reachableMethodsForSCC.Add >> ignore) reachableMethods.[loc]
        let targets = cfg.graph.[current]
        Seq.iter helper targets

    let commitReachableInfo (cfg : cfg) (reachableLocsForSCC : HashSet<codeLocation>) (reachableMethodsForSCC : HashSet<MethodBase>) (current : offset) =
        let currentLoc = {offset = current; method = cfg.methodBase}
        reachableLocations.[currentLoc] <- (reachableLocsForSCC)
        reachableMethods.[currentLoc] <- (reachableMethodsForSCC)

    let initReachableInfo (cfg : cfg) (current : offset) =
        let currentLoc = {offset = current; method = cfg.methodBase}
        reachableLocations.Add(currentLoc, HashSet())
        reachableMethods.Add(currentLoc, HashSet())
    let buildReachabilityInfo (currentMethod : MethodBase) : HashSet<MethodBase> =
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

    let addCall (current : MethodBase) (calledMethods : MethodBase HashSet) =
        let add m (ms : MethodBase HashSet) (d : Dictionary<_, MethodBase HashSet >) =
            if d.ContainsKey m then d.[m].AddAll(ms)
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

                exit processedMethods (methodsQueue @ List.ofSeq calledMethods)
        findFixPoint ([],[]) entryMethod

    let makeTransitiveClosure () =
        let findReachableMethodsForMethod (current : MethodBase) =
            Logger.info "Iterating for %O" current
            methodsReachabilityTransitiveClosure.Add(current, HashSet())
            let used = HashSet<MethodBase>()
            let rec dfs (v : MethodBase) =
                if used.Contains v then ()
                else
                    used.Add(v) |> ignore
//                    if List.con
                    methodsReachabilityTransitiveClosure.[current].Add(v) |> ignore
                    Seq.iter dfs (methodsReachability.[v])
            Seq.iter dfs methodsReachability.[current]
        Seq.iter findReachableMethodsForMethod (methodsReachability.Keys)
    let print () =
        Logger.warning "Calculated CFG Reachability\n"
        methodsReachabilityTransitiveClosure |> Seq.iter (fun kvp ->
            let value = Seq.fold (fun (sb : StringBuilder) m -> sb.AppendFormat("{0}; ", m.ToString())) (StringBuilder()) kvp.Value
            Logger.warning "key = %O; Value = %s" kvp.Key (value.ToString()))

    interface INewSearcher with
        override x.CanReach(ipStack : ip list, target : ip, blocked : ip list) = true
//            (currentSearcher :> INewSearcher).CanReach()
//            Seq.fold (fun acc (s : OneTargetedSearcher) -> acc || (s :> INewSearcher).CanReach(ipStack, target, blocked)) false searchers
        override x.MaxBound = maxBound
        override x.AppendNewStates states =
            let appendStateToSearcher states (s : OneTargetedSearcher) =
                let s = s :> INewSearcher
                s.AppendNewStates states

            let canBePropagated (s : cilState) =
                not (isIIEState s || isUnhandledError s) && isExecutable s
            let states = states |> Seq.filter canBePropagated
            Option.map (appendStateToSearcher states) currentSearcher |> ignore
        override x.Init(mainM, locs) =
            let createSearcher () =
                match locs with
                | [] -> __notImplemented__()
                | l :: _ ->
                    let cfg = CFG.findCfg l.method
                    let s = OneTargetedSearcher(maxBound, l, cfg, reachableLocations, reachableMethods, methodsReachabilityTransitiveClosure)
                    currentSearcher <- Some s

            (x :> INewSearcher).Reset()
            entryMethod <- mainM
            buildReachability ()
            makeTransitiveClosure ()
            print()
            createSearcher ()
        override x.Reset() =
//            Logger.warning "steps number done by TS = %d" stepsNumber
//            stepsNumber <- 0u
            Logger.warning "steps number done by %O = %d" (x.GetType()) stepsNumber
            stepsNumber <- 0u
            currentSearcher <- None
            currentLoc <- noLoc
//            searchers.Clear()
            reachableLocations.Clear()
            reachableMethods.Clear()
            methodsReachability.Clear()
            methodsReachabilityTransitiveClosure.Clear()
//            loc2Searcher.Clear()
            entryMethod <- null
        override x.ChooseAction(qf,qb,pobs,mainId) =
            let tryFindState () =
                match currentSearcher with
                | None -> Stop
                | Some s ->
                    match s.GetNext() with
                    | None -> Stop
                    | Some s ->
                        stepsNumber <- stepsNumber + 1u
                        GoForward s


//            let tryFindState () =
//                    match priorityQueue.IsEmpty with
//                    | true -> None
//                    | _ ->
//                        let s = priorityQueue.FindMin()
//
//                        priorityQueue.DeleteMin() |> ignore
//                        Some s

            match qf, qb, pobs with
            | Seq.Empty, _, _ when stepsNumber = 0u -> Start(Instruction(0, mainId.Method))
            | _, Seq.Cons(b, _), _ ->
                GoBackward(b)
            | _, _, Seq.Empty -> Stop
            | _, Seq.Empty, Seq.Cons(p, _) ->
                let ploc = MyUtils.ip2codeLocation p.loc |> Option.get
                if  ploc = currentLoc then
                    tryFindState()
//                    let s = Seq.fold tryFindAction None searchers
//                    match s with
//                    | None -> Stop
//                    | Some s ->
//                        stepsNumber <- stepsNumber + 1u
//                        GoForward s
                else
                    currentLoc <- ploc
                    let cfg = CFG.findCfg ploc.method
                    let newSearcher = OneTargetedSearcher(maxBound, ploc, cfg, reachableLocations, reachableMethods, methodsReachabilityTransitiveClosure)
                    (newSearcher :> INewSearcher).AppendNewStates qf
                    currentSearcher <- Some <| newSearcher
                    tryFindState()

//                let s = tryFindState ()
//                match s with
//                | None -> Stop
//                | Some s ->
//                    stepsNumber <- stepsNumber + 1u
//                    GoForward s




