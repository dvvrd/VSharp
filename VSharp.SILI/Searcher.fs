namespace VSharp.Interpreter.IL

open System.Collections.Generic
open System.Reflection
open VSharp
open CilStateOperations
open VSharp.Core



type IndexedQueue() =
    let q = List<cilState>()
//    let isRecursiveEffect (s : cilState) =
//        let isEffect = (Seq.last s.state.frames).isEffect
//        if isEffect then
//            let effectsMethod = (Seq.last s.state.frames).func.Method
//            match currentIp s with
//            | {label = Instruction offset; method = m} when Instruction.isDemandingCallOpCode (Instruction.parseInstruction m offset)->
//                let callSite = Instruction.parseCallSite m offset
//                callSite.calledMethod.Equals(effectsMethod)
//            | _ -> false
//        else false
    member x.Add (s : cilState) =
        if List.length s.ipStack <> Memory.CallStackSize s.state then __unreachable__() // TODO: change to assert; this falls in factAgain #do
        q.Add s

    member x.Remove s =
        let removed = q.Remove s
        if not removed then Logger.trace "CilState was not removed from IndexedQueue:\n%O" s
    member x.GetStates () = List.ofSeq q

type SearchDirection =
    | Stop
    | Start of ip
    | GoForward of cilState
    | GoBackward of pob * cilState

type INewSearcher =
    abstract member ChooseAction : cilState seq * (pob * cilState) seq * pob seq * IFunctionIdentifier -> SearchDirection
    abstract member CanReach : ip stack * ip * ip list -> bool
    abstract member Reset : unit -> unit
//    abstract member ClosePob : pob -> unit
    abstract member Init : MethodBase * codeLocation list -> unit
    abstract member AppendNewStates : cilState seq -> unit
    abstract member MaxBound : int

[<AbstractClass>]
type ForwardSearcher(maxBound) = // TODO: max bound is needed, when we are in recursion, but when we go to one method many time -- it's okay #do
//    let maxBound = 10u // 10u is caused by number of iterations for tests: Always18, FirstEvenGreaterThen7
    let mutable stepsNumber = 0u
    interface INewSearcher with
        override x.CanReach(_,_,_) = true
        override x.MaxBound = maxBound
        override x.Init (_,_) = ()
//        override x.ClosePob (_) = ()
        override x.Reset () =
            Logger.warning "steps number done by %O = %d" (x.GetType()) stepsNumber
            stepsNumber <- 0u
        override x.AppendNewStates _ = ()
        override x.ChooseAction(fq, bq, pobs, mainId) =
            match fq, bq with
            | _, Seq.Cons(ps, _) -> GoBackward ps
            | Seq.Empty, Seq.Empty when stepsNumber = 0u -> Start <| Instruction(0, mainId.Method)
            | _, Seq.Empty ->
                match x.PickNext fq with
                | None -> Stop
                | Some s ->
                    stepsNumber <- stepsNumber + 1u
                    GoForward s

    abstract member PickNext : cilState seq -> cilState option
    default x.PickNext (qf : cilState seq) = None
    member x.Used (cilState : cilState) =
        let maxBound : int = (x :> INewSearcher).MaxBound
        match currentIp cilState with
        | Instruction(offset, m) ->
            let codeLocation = {offset = offset; method = m}
            match PersistentDict.tryFind cilState.level codeLocation with
            | Some current -> current >= uint32 maxBound
            | None -> false
        | _ -> false


type BFSSearcher(maxBound) =
    inherit ForwardSearcher(maxBound) with
        override x.PickNext fq =
            let canBePropagated (s : cilState) =
                not (isIIEState s || isUnhandledError s) && isExecutable s && not (x.Used s)
            let states = fq |> Seq.filter canBePropagated
            match states with
            | Seq.Cons(x, _) -> Some x
            | Seq.Empty -> None

type DFSSearcher(maxBound) =
    inherit ForwardSearcher(maxBound) with
        override x.PickNext fq =
            let canBePropagated (s : cilState) =
                not (isIIEState s || isUnhandledError s) && isExecutable s && not (x.Used s)
            let states = fq |> Seq.filter canBePropagated
            match states with
            | Seq.Cons(_, _) -> Seq.last states |> Some
            | Seq.Empty -> None
