namespace VSharp.Interpreter.IL

open System
open System.Collections.Generic
open FSharpx.Collections

open VSharp
open VSharp.Core
open ipOperations
open CilStateOperations

type public PobsInterpreter(searcher : INewSearcher) =
    inherit ExplorerBase()
    let infty = Int32.MaxValue
    let GlobalBound = 200
    let initialOpStackSize = 0u
    let qFront = List<cilState>()
    let qBack = List<pob * cilState>()
    let transition = Dictionary<ip, cilState list>()
//    let witnesses = Dictionary<pob, cilState list>()
//    let blockedLocs = Dictionary<pob, ip list>()
    let possiblePobsLocs = List<ip>()
//    let sPobs = Dictionary<cilState, pob list>()
    let mutable curLvl = searcher.MaxBound
    let mainPobs = List<pob>()
    let currentPobs = List<pob>()
    let loc2pob = Dictionary<ip, List<pob>>()
    let answeredPobs = Dictionary<pob, pobStatus>()
//    let ignoredPobs = HashSet<pob>()
    let parents = Dictionary<pob, pob>()
//    let canReach state (loc : ip) (blockedLocs : ip list) =
//        //TODO: use CFG-reachability analysis
//        searcher.CanReach (state, loc, blockedLocs)
    let addToDictionaryWithListValue (d : Dictionary<'a, 'b list>) k elem =
        let v = d.GetValueOrDefault(k, [])
        d.[k] <- (elem :: v)

//    let removeFromDictionaryWithListValue (d : Dictionary<'a, 'b list>) k elem =
//        let v = d.GetValueOrDefault(k, [])
//        let v' = List.filter (fun x -> x <> elem) v
//        d.[k] <- v'

//    let removeFromGlobalVars (s : cilState, p : pob) =
//        removeFromDictionaryWithListValue sPobs s p
//        removeFromDictionaryWithListValue witnesses p s

//    let addWitness(s : cilState, p : pob) =
//        if ignoredPobs.Contains p then () else
//        let sLvl = levelToInt s.level
//        try
//            if sLvl <= p.lvl && canReach s.ipStack p.loc blockedLocs.[p] then
//                addToDictionaryWithListValue witnesses p s
//                addToDictionaryWithListValue sPobs s p
//            else
//                let res = sLvl <= p.lvl
//                let res2 = canReach s.ipStack p.loc blockedLocs.[p]
//                Logger.info "state with ipStack = %O is not witnessing pob = %O" s.ipStack p
//                Logger.info "state.Lvl <= p.lvl = %O" res
//                Logger.info "canReach = %O" res2
//        with
//        | :? KeyNotFoundException -> __notImplemented__()
//    let rec blockWitness(s', p') =
////        removeFromGlobalVars(s', p')
//        match List.exists (fun (s : cilState) -> s.startingIP = s'.startingIP) witnesses.[p'] with
//        | true -> ()
//        | false ->
//            addToDictionaryWithListValue blockedLocs p' s'.startingIP
//            List.iter (fun (s : cilState) ->
//                if not <| canReach s.ipStack p'.loc blockedLocs.[p'] then blockWitness(s, p')) witnesses.[p']

    let doAddPob (pob : pob) =
        currentPobs.Add(pob)
        let mutable pobsRef = ref null
        if not <| loc2pob.TryGetValue(pob.loc, pobsRef) then
            pobsRef <- ref (List<pob>())
            loc2pob.Add(pob.loc, !pobsRef)
        (!pobsRef).Add pob


    let addPob(parent : pob, child : pob) =
        assert(parents.ContainsKey(child) |> not)
        parents.Add(child, parent)
        doAddPob child
//        currentPobs.Add child
//        blockedLocs.Add(child, [])
//        Seq.iter (fun s -> addWitness(s, child)) qFront
        Seq.iter (fun s -> qBack.Add(child, s)) transition.[child.loc]

    let rec answerYes (s' : cilState, p' : pob) =
//        ignoredPobs.Add(p') |> ignore
//        let removed = currentPobs.Remove(p') in assert(removed)
//        let removed = witnesses.Remove(p') in Logger.warning "Removing from witnesses %O" p' ; assert(removed)
//        let removed = blockedLocs.Remove(p') in assert(removed)
        if (not <| loc2pob.ContainsKey(p'.loc)) then
            assert(mainPobs.Contains p')
        else
            let list = loc2pob.[p'.loc]
            list.Remove(p')  |> ignore
            if list.Count = 0 then loc2pob.Remove(p'.loc) |> ignore
        currentPobs.Remove(p') |> ignore
//        witnesses.Remove(p')  |> ignore
//        blockedLocs.Remove(p') |> ignore
        qBack.RemoveAll(fun (p, _) -> p = p') |> ignore
        if Seq.contains p' mainPobs then
            mainPobs.Remove(p') |> ignore
        if answeredPobs.ContainsKey p' |> not then answeredPobs.Add(p', Witnessed s')
        else answeredPobs.[p'] <- Witnessed s'
//        removeFromGlobalVars(s', p')
        if parents.ContainsKey p' then
            if p' = parents.[p'] then internalfailf "kek"
            answerYes(s', parents.[p'])

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
        searcher.AppendNewStates [start]
//        Seq.iter (fun p -> addWitness(start, p)) currentPobs

    member x.Forward (s : cilState) =
//        if before > (levelToInt s.level) then ()
//        else before <- (levelToInt s.level)
//        Logger.warning "s.lvl = %d" (levelToInt s.level)
//        assert(sPobs.ContainsKey s)
//        match sPobs.[s] with
//        | [] -> ()
//        | _ -> ()
//        if qFront.Count <> 1 then internalfailf "kek"
//        let removed = qFront.Remove(s) in assert(removed)
        let removed = qFront.RemoveAll(fun s' -> LanguagePrimitives.PhysicalEquality s s') in assert(removed > 0)
        let goodStates, incompleteStates, errors = ILInterpreter(x).ExecuteOnlyOneInstruction s
        let goodStates = goodStates |> List.filter (fun s -> levelToInt s.level <= curLvl)
        if List.isEmpty goodStates then ()
        qFront.AddRange (goodStates @ incompleteStates @ errors)

        searcher.AppendNewStates(goodStates)
        goodStates |> List.iter (fun (s' : cilState) ->
//            if not <| sPobs.ContainsKey(s') then sPobs.Add(s', [])
            let ip' = currentIp s'
            if Seq.contains ip' possiblePobsLocs then addToDictionaryWithListValue transition ip' s'
            let pobsList = ref null
            if loc2pob.TryGetValue(currentIp s', pobsList) then
                !pobsList |> Seq.iter (fun p -> qBack.Add(p, s'))
//            sPobs.[s] |> List.iter (fun p ->
//                addWitness(s', p)
//                assert(sPobs.ContainsKey s')
//                if p.loc = currentIp s' then qBack.Add(p, s')                )
//        )
//        List.iter (fun (p : pob) -> if p.loc <> currentIp s then removeFromGlobalVars(s, p)) sPobs.[s]
        )

    member x.OverApproximate(_ : ip, _ : int) : term = Terms.True

    member x.Backward (p' : pob, s' : cilState, EP : ip) =
        let removed = qBack.Remove(p',s') in assert(removed)
        assert(currentIp s' = p'.loc)
        let lvl = p'.lvl - (levelToInt s'.level)
        let fml = Memory.WLP s'.state p'.fml
        match Memory.IsSAT fml with
        | true when s'.startingIP = EP ->
            answerYes(s', p')
        | true ->
            let p = {loc = s'.startingIP; lvl = lvl; fml = fml}
            addPob(p', p)
        | false ->
            Logger.info "UNSAT for pob = %O and s' = %O" p' s'
    member x.PropDirSymExec (mainId : IFunctionIdentifier) (EP : ip) mainPobsList =
//        List.iter (fun p -> mainPobs.Add p; witnesses.Add(p, []); blockedLocs.Add(p, [])) mainPobsList
        List.iter mainPobs.Add mainPobsList
        let createPobs () =
            mainPobs |> Seq.iter (fun (mp : pob) ->
                let p = {mp with lvl = curLvl}
//                blockedLocs.Add(p, [])
//                witnesses.Add(p, [])
                parents.Add(p, mp)
                doAddPob p)
//                currentPobs.Add p)
        while mainPobs.Count > 0 && curLvl <= searcher.MaxBound do
            createPobs()
            while currentPobs.Count > 0 do
                match searcher.ChooseAction(qFront, qBack, currentPobs, mainId) with
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
//        witnesses.Clear()
//        blockedLocs.Clear()
        possiblePobsLocs.Clear()
//        sPobs.Clear()
        mainPobs.Clear()
        currentPobs.Clear()
        answeredPobs.Clear()
        parents.Clear()
//        searcher.Reset()
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
        searcher.Init(entryMethodId.Method, codeLocations)
        x.PropDirSymExec entryMethodId EP mainPobs
        searcher.Reset()
        let showResultFor (mp : pob) =
            match answeredPobs.[mp] with
            | Unreachable -> Logger.info "NO: MainPob = %O" mp
            | Witnessed s -> Logger.info "YES: MainPob = %O, witness = %O" mp s
            | Unknown -> Logger.info "Unknown: MainPob = %O" mp
//        List.iter showResultFor mainPobs
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

