namespace VSharp.Analyzer

open System
open System.Reflection
open System.Collections.Generic
open System.Reflection.Emit
open VSharp.Interpreter.IL
open FSharpx.Collections
open VSharp
open VSharp.Core
open CilStateOperations
open ipOperations

module internal TermUtils =

    let term (t : term) = t.term

    let getAddressTermFromRefOrPtr getTerm refOrPtr =
        let rec getLastAddress = function
            | StructField(addr, _) -> getLastAddress addr
            | addr -> addr
        let getAddressTerm = term >> function
            | Ptr(Some addr, _, _)
            | Ref addr -> getLastAddress addr |> getTerm
            | _ -> __unreachable__()
        GuardedApplyExpression refOrPtr getAddressTerm

    let isConcrete (term : term) =
        match term.term with
        | Concrete _ -> true
        | _ -> false

    let (|ConcreteHeapAddress|_|) = term >> (|ConcreteHeapAddress|_|)
    let isConcreteHeapAddress = function
        | ConcreteHeapAddress _ -> true
        | _ -> false

    let rec isConcreteAddress (address : address) =
        match address with
        | PrimitiveStackLocation _
        | BoxedLocation _
        | StaticField _ -> true
        | StackBufferIndex (_, term) -> isConcrete term
        | StructField (address, _) -> isConcreteAddress address
        | ClassField (heapAddress, _)
        | ArrayIndex (heapAddress, _, _)
        | ArrayLowerBound (heapAddress, _, _)
        | ArrayLength (heapAddress, _, _) -> isConcreteHeapAddress heapAddress

    let isConcretePtr = function
        | Ptr(None, _, None) -> true
        | Ptr(None, _, Some shift) -> isConcrete shift
        | Ptr(Some address, _, None) -> isConcreteAddress address
        | Ptr(Some address, _, Some shift) -> isConcreteAddress address && isConcrete shift
        | _ -> false

[<StructuralEquality;NoComparison>]
type evaluationStackSource =
    {shift : uint32; typ : symbolicType; time : vectorTime}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.time
        override x.TypeOfLocation = x.typ
        override x.Compose state =
            let result = EvaluationStack.GetItem (int x.shift) state.evaluationStack
            assert(Types.CanCastImplicitly result x.typ)
            Types.Cast result x.typ

[<StructuralEquality;NoComparison>]
type stackBufferIndexAddress =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = Types.IndexType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | StackBufferIndex(_, term) -> term
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type classFieldAddress =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ClassField(term, _) -> term
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type arrayIndexHeapAddress =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ArrayIndex(term, _, _) -> term
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type arrayIndexItem =
    {baseSource : IMemoryAccessConstantSource; i : int}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ArrayIndex(_, indices, _) -> List.item x.i indices
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type arrayLowerBoundHeapAddress =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ArrayLowerBound(term, _, _) -> term
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type arrayLowerBoundDimension =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ArrayLowerBound(_, dim, _) -> dim
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type arrayLengthAddress =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ArrayLength(term, _, _) -> term
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type arrayLengthDimension =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getTerm = function
                | ArrayLength(_, dim, _) -> dim
                | _ -> __unreachable__()
            TermUtils.getAddressTermFromRefOrPtr getTerm baseTerm

[<StructuralEquality;NoComparison>]
type pointerShift =
    {baseSource : IMemoryAccessConstantSource}
    interface IMemoryAccessConstantSource with
        override x.SubTerms = Seq.empty
        override x.Time = x.baseSource.Time
        override x.TypeOfLocation = AddressType
        override x.Compose state =
            let baseTerm = x.baseSource.Compose state
            let getShift term =
                match term.term with
                | Ptr(_, _, Some shift) -> shift
                | _ -> __unreachable__()
            GuardedApplyExpression baseTerm getShift

module Properties =
    let internal exitVertexOffset = -1
    let internal exitVertexNumber = -1

    let internal initialVertexOffset = 0
    let internal initialVertexNumber = 0

module public CFA =
    open TermUtils

    let pushNewObjResultOnEvaluationStack (cilState : cilState) reference (calledMethod : MethodBase) =
        let valueOnStack =
            if calledMethod.DeclaringType.IsValueType then
                  Memory.ReadSafe cilState.state reference
            else reference
        push valueOnStack cilState

    type Vertex private(id, m : MethodBase, ip : ip, evaluationStack : evaluationStack) = // TODO: delete all code with vertex #do
        static let ids : Dictionary<MethodBase, int> = Dictionary<_,_>()
        let lemmas = Lemmas(m, ip)
        let paths = Paths(m, ip)
        let queries = Queries(m, ip)
        let solver = null //Solver.SolverPool.mkSolver()
        let errors = List<cilState>()
        let incomingEdges: List<Edge> = List<_>()
        let outgoingEdges: List<Edge> = List<_>()

        override x.GetHashCode() = (m, ip).GetHashCode()
        override x.Equals(o : obj) =
            match o with
            | :? Vertex as other -> x.Method = other.Method && x.Ip = other.Ip
            | _ -> false
        interface IComparable with
            override x.CompareTo(other) =
                match other with
                | :? Vertex as other when x.Method.Equals(other.Method) -> x.GetHashCode().CompareTo(other.GetHashCode())
                | :? Vertex as other -> x.Method.MetadataToken.CompareTo(other.Method.MetadataToken)
                | _ -> -1
        member x.AddErroredStates (newErrors : cilState list) =
            errors.AddRange(newErrors)

        member x.Id with get() = id
        member x.Lemmas = lemmas
        member x.Paths with get () = paths
        member x.Queries = queries
        member x.Solver = solver
        member x.IncomingEdges = incomingEdges
        member x.OutgoingEdges = outgoingEdges
        member x.Ip with get() = ip
        member x.EvaluationStack with get() = evaluationStack
        member x.Method with get() = m
        member x.IsMethodStartVertex with get() =
            match ip with
            | Instruction(0, _) -> true
            | _ -> false
        member x.IsMethodExitVertex with get() =
            match ip with
            | Exit _ -> true
            | _ -> false
        override x.ToString() =
            sprintf "(Method = %O, ip = %O, id = %d)\n" m ip id +
            sprintf "Edges count = %d\n" x.OutgoingEdges.Count +
            "Edges: \n" + Seq.fold (fun acc edge -> acc + edge.ToString() + "\n") "" x.OutgoingEdges
        static member CreateVertex method offset evaluationStack =
            let id = Dict.getValueOrUpdate ids method (always 0)
            ids.[method] <- id + 1
            Vertex(id, method, offset, evaluationStack)
    and
        [<AbstractClass>]
        Edge(src : Vertex, dst : Vertex) =
        abstract member Type : string
        abstract member PropagatePath : cilState -> cilState list
        member x.PrintLog msg obj = Logger.trace "[%s] %s: %O" (x.commonToString()) msg obj
        member x.Src = src
        member x.Dst = dst
        member x.Method = x.Src.Method
        member x.CommonFilterStates = not << IsFalsePathCondition
        override x.ToString() = x.commonToString()
        member x.commonToString() =
            sprintf "%s ID:[%d --> %d] IP:[%O --> %O] Method:%s"
                x.Type x.Src.Id x.Dst.Id x.Src.Ip x.Dst.Ip (Reflection.getFullMethodName x.Method)


    type 'a unitBlock =
        {
            entity : 'a
            entryPoint : Vertex
            exitVertex : Vertex
            vertices : Dictionary<int, Vertex>
        }
        with
        member x.AddVertex (v : Vertex) =
            if not <| x.vertices.ContainsKey v.Id then
                x.vertices.Add(v.Id, v)
        member x.WithEntryPoint v = {x with entryPoint = v}
        member x.WithExitVertex v = {x with exitVertex = v}
        member x.FindCallVertex id = x.vertices.[id]

        static member private CreateEmpty entity method entryIp exitIp =
            let entry = Vertex.CreateVertex method entryIp emptyEvaluationStack
            let exit = Vertex.CreateVertex method exitIp emptyEvaluationStack
            let vertices = Dictionary<int, Vertex>()
            vertices.Add(entry.Id, entry)
            vertices.Add(exit.Id, exit)
            {
                entity = entity
                entryPoint = entry
                exitVertex = exit
                vertices = vertices
            }
        static member CreateEmptyForMethod (m : MethodBase) =
            let entry = instruction m Properties.initialVertexOffset
            unitBlock<'a>.CreateEmpty m m entry (exit m)

        static member CreateEmptyForFinallyClause (m : MethodBase) (ehc : ExceptionHandlingClause) =
            let entryOffset = ehc.HandlerOffset
            // TODO: check if this formula is forever true
            let exitOffset = ehc.HandlerOffset + ehc.HandlerLength - 1
            let entry = instruction m entryOffset
            let exit = instruction m exitOffset
            unitBlock<'a>.CreateEmpty ehc m entry exit
        override x.ToString() =
            Seq.fold (fun acc vertex -> acc + "\n" + vertex.ToString()) "" x.vertices.Values

    type cfa =
            {
              cfg : CFG.cfgData
              body : MethodBase unitBlock
              finallyHandlers : Dictionary<offset, ExceptionHandlingClause unitBlock>
            }
        with
            member x.Method = x.cfg.methodBase
            member x.FindOrCreateFinallyHandler (ehc : ExceptionHandlingClause) =
                let offset = ehc.HandlerOffset
                if x.finallyHandlers.ContainsKey offset then x.finallyHandlers.[offset]
                else
                    let block = unitBlock<ExceptionHandlingClause>.CreateEmptyForFinallyClause x.Method ehc
                    x.finallyHandlers.Add(offset, block)
                    block

            member x.WithEntryPoint v = {x with body = x.body.WithEntryPoint v}
            member x.WithExitVertex v = {x with body = x.body.WithExitVertex v}
            member x.WithFinallyEntryPoint offset v = x.finallyHandlers.[offset].WithEntryPoint v |> ignore; x
            member x.WithFinallyExitVertex offset v = x.finallyHandlers.[offset].WithExitVertex v |> ignore; x
            override x.ToString() =
                let separator = "\n"
                "Method: " + x.Method.ToString() + separator +
                x.body.ToString() + separator +
                Seq.fold (fun acc block -> acc + block.ToString() + separator) "" (x.finallyHandlers.Values)



    type StepEdge(src : Vertex, dst : Vertex, effect : cilState) =
        inherit Edge(src, dst)
        override x.Type = "StepEdge"
        override x.PropagatePath (cilState : cilState) =
//            let print cilStates =
//                x.PrintLog "composition left"  <| dump cilState
//                x.PrintLog "composition right" <| dump effect
//                List.iter (dump >> x.PrintLog (sprintf "composition resulted")) cilStates
            let cilStates = compose cilState effect
            // Do NOT turn this List.forall into List.exists to be sure that EVERY returned state is propagated
            assert(List.forall (fun (cilState' : cilState) -> cilState'.state.stack = cilState.state.stack) cilStates)
            let goodStates = List.filter (stateOf >> x.CommonFilterStates) cilStates
            if List.length goodStates <> List.length cilStates
                then Logger.trace "Some states were not propagated from %O to %O" src.Ip cilState.ipStack
//            print goodStates
            goodStates

        member x.Effect = effect
        member x.VisibleVariables() = __notImplemented__()

        override x.ToString() = dump effect

    type CallEdge(src : Vertex, dst : Vertex, callSite : callSite, stateWithArgsOnFrameAndAllocatedType : state, numberToDrop, interpreter : ILInterpreter) =
        inherit Edge(src, dst)
        do
           assert(Memory.CallStackSize stateWithArgsOnFrameAndAllocatedType = 2)
        override x.Type = "Call"
        override x.PropagatePath (cilStateBeforeCall : cilState) =
            let k (cilStates : cilState list) =
                let propagateStateAfterCall acc (resultCilState : cilState) =
                    let resultState = resultCilState.state
                    let initialState = cilStateBeforeCall.state
                    assert(initialState.stack = resultState.stack)
                    x.PrintLog "propagation through callEdge" callSite
//                    x.PrintLog "call edge: composition left" (dump cilStateBeforeCall)
//                    x.PrintLog "call edge: composition result" (dump resultCilState)
                    let stateAfterCall =
                        let _, evaluationStack = EvaluationStack.PopArguments numberToDrop initialState.evaluationStack
                        match resultState.returnRegister with
                        | Some r ->
                            assert(callSite.HasNonVoidResult)
                            { resultState with
                                               returnRegister = None
                                               evaluationStack = EvaluationStack.Push r evaluationStack }
                        | None when callSite.opCode = OpCodes.Newobj ->
                            assert(not callSite.HasNonVoidResult)
                            let reference = Memory.ReadThis stateWithArgsOnFrameAndAllocatedType callSite.calledMethod
                            let modifiedCilState = pushNewObjResultOnEvaluationStack (withEvaluationStack evaluationStack resultCilState) reference callSite.calledMethod
                            modifiedCilState.state
                        | None ->
                            assert(not callSite.HasNonVoidResult)
                            resultState
                    if x.CommonFilterStates stateAfterCall then
                        (resultCilState |> setCurrentIp dst.Ip |> withState stateAfterCall) :: acc
                    else acc
                List.fold propagateStateAfterCall [] cilStates
            let states = Memory.ComposeStates cilStateBeforeCall.state stateWithArgsOnFrameAndAllocatedType
            match states with
            | [state] ->
                let cilState = {cilStateBeforeCall with state = state}
                match callSite.opCode with
                | Instruction.NewObj   when Reflection.isDelegateConstructor callSite.calledMethod -> k [popFrameOf cilState]
                | Instruction.NewObj   when Reflection.isArrayConstructor callSite.calledMethod -> k [popFrameOf cilState]
                | Instruction.Call
                | Instruction.NewObj   ->
                    interpreter.CommonCall callSite.calledMethod cilState k
                | Instruction.CallVirt -> interpreter.CommonCallVirt callSite.calledMethod cilState k // TODO: care about deleagete! #do
                | _ ->  __notImplemented__()
            | _ -> internalfailf "Calling %s: composition with frames unexpectedly forked!" callSite.calledMethod.Name
        member x.ExitNodeForCall() = __notImplemented__()
        member x.CallVariables() = __notImplemented__()
        override x.ToString() =
            sprintf "%s\nstate = %O\n" (base.ToString()) (API.Memory.Dump stateWithArgsOnFrameAndAllocatedType)

    module cfaBuilder =
        let private alreadyComputedCFAs = Dictionary<MethodBase, cfa>()

        [<CustomEquality; CustomComparison>]
        type bypassDataForEdges =
            { u : ip
              srcVertex : Vertex
              v : ip
              uOut : int
              vOut : int
              minSCCs : int
              evaluationStack : evaluationStack
              allocatedTypes : pdict<concreteHeapAddress, symbolicType>
              lengths : pdict<arrayType, vectorRegion>
              lowerBounds : pdict<arrayType, vectorRegion>
            }
            override x.ToString() =
                let emptyState = {API.Memory.EmptyState with evaluationStack = x.evaluationStack }
                sprintf "u = %O, id = %d; v = %O; state = %s" x.u x.srcVertex.Id x.v (Memory.Dump emptyState)
            override x.GetHashCode() = (x.u, x.v, x.srcVertex).GetHashCode()
            override x.Equals y =
                match y with
                | :? bypassDataForEdges as y -> x.u = y.u && x.srcVertex.Equals(y.srcVertex) && x.v = y.v && x.evaluationStack = y.evaluationStack
                | _ -> false
            interface IComparable with
                override x.CompareTo (obj : obj) =
                    let compareData a1 a2 a3 b1 b2 b3 =
                        if a1 > b1 || a1 = b1 && a2 > b2 || a1 = b1 && a2 = b2 && a3 > b3 then -1
                        elif a1 = b1 && a2 = b2 && a3 = b3 then 0
                        else 1
                    match obj with
                    | :? bypassDataForEdges as other -> compareData x.minSCCs x.uOut x.vOut other.minSCCs other.uOut other.vOut
                    | _ -> -1

        let private createEmptyCFA cfg method =
            {
              cfg = cfg
              body = unitBlock<MethodBase>.CreateEmptyForMethod method
              finallyHandlers = Dictionary<_,_>()
            }

        let private addEdge (edge : Edge) =
            edge.Src.OutgoingEdges.Add edge
            edge.Dst.IncomingEdges.Add edge

        let internal shouldRemainEvaluationStack (term : term) =
            match term.term with
            | Concrete _ -> true
            | Ref addr -> isConcreteAddress addr
            | Ptr _ as v -> isConcretePtr v
            | HeapRef(heapAddress, _) -> isConcreteHeapAddress heapAddress
            | _ -> false

        let private updateLI makeSource term name typ =
            let isConcrete =
                match typ with
                | AddressType -> isConcreteHeapAddress
                | _ when Types.IsInteger typ -> isConcrete
                | _ -> __notImplemented__()
            if isConcrete term then term
            else Constant name (makeSource()) typ

        let rec private makeSymbolicAddress source = function
            | StackBufferIndex(key, term) when isConcrete term |> not ->
                let source : stackBufferIndexAddress = {baseSource = source}
                StackBufferIndex(key, Constant "StackBufferIndex" source Types.IndexType)
            | StructField(address, fieldId) ->
                StructField(makeSymbolicAddress source address, fieldId)
            | ClassField(heapAddress, fieldId) when isConcreteHeapAddress heapAddress |> not ->
                let source : classFieldAddress = {baseSource = source}
                ClassField(Constant "ClassFieldAddress" source AddressType, fieldId)
            | ArrayIndex(heapAddress, indices, aType) ->
                let makeAddressSource () : arrayIndexHeapAddress = {baseSource = source}
                let address = updateLI makeAddressSource heapAddress "ArrayIndexHeapAddress" AddressType
                let makeIndexSource i () : arrayIndexItem = {baseSource = source; i = i}
                let indexName i = sprintf "ArrayIndex.[%d]" i
                let indices = List.mapi (fun i x -> updateLI (makeIndexSource i) x (indexName i) Types.IndexType) indices
                ArrayIndex(address, indices, aType)
            | ArrayLowerBound(heapAddress, dim, aType) ->
                let makeAddressSource () : arrayLowerBoundHeapAddress = {baseSource = source}
                let address = updateLI makeAddressSource heapAddress "ArrayLowerBoundHeapAddress" AddressType
                let makeDimSource () : arrayLowerBoundDimension = {baseSource = source}
                let dim = updateLI makeDimSource dim "ArrayLowerBoundDimension" Types.IndexType
                ArrayLowerBound(address, dim, aType)
            | ArrayLength(heapAddress, dim, aType) ->
                let makeAddressSource () : arrayLengthAddress = {baseSource = source}
                let address = updateLI makeAddressSource heapAddress "ArrayLengthAddress" AddressType
                let makeDimSource () : arrayLengthDimension = {baseSource = source}
                let dim = updateLI makeDimSource dim "ArrayLengthDimension" Types.IndexType
                ArrayLength(address, dim, aType)
            | address -> address

        let makeFunctionResultConstant state (t : System.Type) =
            let typ = Types.FromDotNetType t
            let source = {shift = 1u; typ = typ; time = state.currentTime}
            let name = sprintf "FunctionResult of type = %O" t
            Memory.MakeSymbolicValue source name typ

        let makeSymbolicEvaluationStack time (evaluationStack : evaluationStack) : evaluationStack =
            let mkSource (index : int) typ =
                {shift = uint32 index; typ = typ; time = time}

            let makeSymbolic index (v : term) =
                if shouldRemainEvaluationStack v then v
                else
                    let shift = index
                    let typ = TypeOf v
                    let source = mkSource shift typ
                    let name = sprintf "evaluationStack.[%d] from top" shift
                    match v.term with
                    | Ref address ->
                        makeSymbolicAddress source address |> Ref
                    | Ptr(address, typ, shift) ->
                        let addr = Option.map (makeSymbolicAddress source) address
                        let makeShiftSource () : pointerShift = {baseSource = source}
                        let shift = Option.map (fun shift -> updateLI makeShiftSource shift "PointerShift" Types.IndexType) shift
                        Ptr addr typ shift
                    | _ -> Memory.MakeSymbolicValue source name typ

            let symbolicEvaluationStack = EvaluationStack.MakeSymbolicActiveFrame makeSymbolic evaluationStack
            symbolicEvaluationStack

        let private executeSeparatedOpCode (methodInterpreter : MethodInterpreter) (cfg : cfg) (cilState : cilState) =
            let ip = currentIp cilState
            let offset =
                ip.Offset()
            let opCode, calledMethod = cfg.offsetsDemandingCall.[offset]
            let callSite = { sourceMethod = cfg.methodBase; offset = offset; calledMethod = calledMethod; opCode = opCode }
            let pushFunctionResultOnEvaluationStackIfNeeded (cilState : cilState) (methodInfo : MethodInfo) =
                if methodInfo.ReturnType = typeof<System.Void> then cilState
                else push (makeFunctionResultConstant cilState.state methodInfo.ReturnType) cilState

            let args, cilStateWithoutArgs = InstructionsSet.retrieveActualParameters calledMethod cilState
            let this, cilState =
                match calledMethod with
                | _ when opCode = OpCodes.Newobj ->
                    let ilInterpreter = ILInterpreter(methodInterpreter)
                    let cilStates = ilInterpreter.CommonNewObj false (calledMethod :?> ConstructorInfo) cilStateWithoutArgs args id
                    assert (List.length cilStates = 1)
                    let cilState = List.head cilStates
                    assert(Option.isSome cilState.state.returnRegister)
                    let reference = Option.get cilState.state.returnRegister
                    let cilState = pushNewObjResultOnEvaluationStack cilState reference calledMethod
                    Some reference, withNoResult cilState
                | :? ConstructorInfo -> pop cilStateWithoutArgs |> mapfst Some
                | :? MethodInfo as methodInfo when not calledMethod.IsStatic ->
                    let this, cilState = pop cilStateWithoutArgs
                    Some this, pushFunctionResultOnEvaluationStackIfNeeded cilState methodInfo
                | :? MethodInfo as methodInfo ->
                    None, pushFunctionResultOnEvaluationStackIfNeeded cilStateWithoutArgs methodInfo
                | _ -> internalfailf "unknown methodBase %O" calledMethod

            let numberToDrop = List.length args + if Option.isNone this || callSite.opCode = OpCodes.Newobj then 0 else 1
            let stateWithArgsOnFrame = ExplorerBase.ReduceFunctionSignature cilState.state (methodInterpreter.MakeMethodIdentifier calledMethod) this (Some args) id
            let nextIp =
                assert(cfg.graph.[offset].Count = 1)
                match ip with
                | Instruction(_, m) -> Instruction(cfg.graph.[offset].[0], m)
                | _ -> __notImplemented__()

            let cilState = cilState |> setCurrentIp nextIp |> withState stateWithArgsOnFrame
            cilState, callSite, numberToDrop

        let private createVertexIfNeeded methodBase evaluationStack (v : ip) (vertices : pdict<ip * evaluationStack, Vertex>) =
            let concreteEvaluationStack = EvaluationStack.FilterActiveFrame shouldRemainEvaluationStack evaluationStack
            if PersistentDict.contains (v, concreteEvaluationStack) vertices then
                PersistentDict.find vertices (v, concreteEvaluationStack), vertices
            else
                let dstVertex = Vertex.CreateVertex methodBase v evaluationStack
                dstVertex, PersistentDict.add (v, concreteEvaluationStack) dstVertex vertices

        let updateQueue (cfg : cfg) newU (d : bypassDataForEdges) (q, used) =
            let changeData w =
                match w with
                | Instruction(wOffset, _) -> {d with v = w; vOut = cfg.dfsOut.[wOffset]; minSCCs = min cfg.sccOut.[wOffset] cfg.sccOut.[wOffset]}
                | Exit _ -> {d with v = w; vOut = -1; minSCCs = -1}
                | _ -> __notImplemented__()
            let addIfNotUsed (q, used) d =
                if PersistentSet.contains d used then q, used
                else PriorityQueue.insert d q, PersistentSet.add used d
            match newU with
            | Exit _ -> q, used
            | Instruction(offset, m) when cfg.graph.[offset].Count = 0 -> (changeData (Exit m)) |> addIfNotUsed (q, used)
            | Instruction(vOffset, m) -> cfg.graph.[vOffset] |> Seq.fold (fun acc wOffset -> changeData (instruction m wOffset) |> addIfNotUsed acc) (q, used)
            | _ -> __notImplemented__()

        let addEdgeAndRenewQueue createEdge (d : bypassDataForEdges) (cfg : cfg) (currentTime, vertices, q, used) (cilState' : cilState) =
            let s' = cilState'.state
            let dstIp = currentIp cilState'
            let dstVertex, vertices = createVertexIfNeeded cfg.methodBase s'.evaluationStack dstIp vertices
            addEdge <| createEdge cilState' dstVertex

            let bypassData = {d with u = dstIp; srcVertex = dstVertex; uOut = d.vOut; evaluationStack = s'.evaluationStack
                                     allocatedTypes = s'.allocatedTypes; lengths = s'.lengths; lowerBounds = s'.lowerBounds }
            let newQ, newUsed =
                match cilState'.iie with
                | None -> updateQueue cfg dstIp bypassData (q, used)
                | Some _ -> q, used
            VectorTime.max currentTime s'.currentTime, vertices, newQ, newUsed

        let private isConcreteHeapRef (term : term) =
            match term.term with
            | HeapRef(addr, _) -> isConcreteHeapAddress addr
            | _ -> false

        let private getTermConcreteHeapAddress (term : term) =
            match term.term with
            | HeapRef(ConcreteHeapAddress addr, _) -> addr
            | _ -> __unreachable__()

        let private prepareStateWithConcreteInfo (s : state) (d : bypassDataForEdges) =
            let concreteHeapAddresses = s.evaluationStack |> EvaluationStack.ToList |> List.filter isConcreteHeapRef |> List.map getTermConcreteHeapAddress
            let appendAllocatedTypes acc k v = if List.contains k concreteHeapAddresses then PersistentDict.add k v acc else acc
            let allocatedTypes = PersistentDict.fold appendAllocatedTypes PersistentDict.empty d.allocatedTypes
            let allocatedTypesValues = PersistentDict.values allocatedTypes

            let appendLengths acc ((t,_,_) : arrayType as k) v = if Seq.contains t allocatedTypesValues then PersistentDict.add k v acc else acc
            let appendLowerBounds acc ((t,_,_) : arrayType as k) v = if Seq.contains t allocatedTypesValues then PersistentDict.add k v acc else acc

            let lengths = PersistentDict.fold appendLengths PersistentDict.empty d.lengths
            let lowerBounds = PersistentDict.fold appendLowerBounds PersistentDict.empty d.lowerBounds
            {s with allocatedTypes = allocatedTypes; lengths = lengths; lowerBounds = lowerBounds}

        // note: entry point and exit vertex must be added to unit block
        let private computeCFAForBlock (methodInterpreter : MethodInterpreter) (initialState : state) (cfa : cfa) (block : unitBlock<'a>) =
            let ilInterpreter = ILInterpreter(methodInterpreter)
            let cfg = cfa.cfg
            let rec bypass (cfg : cfg) (q : IPriorityQueue<bypassDataForEdges>) (used : pset<bypassDataForEdges>) (vertices : pdict<ip * evaluationStack, Vertex>) currentTime =
                let d, q = PriorityQueue.pop q
                assert(PersistentSet.contains d used)
                let srcVertex = d.srcVertex
                assert(not <| isExit d.u)
                let offset = d.u.Offset()

                let currentTime = VectorTime.advance currentTime
                let symbolicEvaluationStack = makeSymbolicEvaluationStack currentTime d.evaluationStack
                let modifiedState = prepareStateWithConcreteInfo {initialState with currentTime = currentTime; startingTime = currentTime; evaluationStack = symbolicEvaluationStack} d

                let initialCilState = makeCilState d.u (uint32 <| EvaluationStack.Length symbolicEvaluationStack) modifiedState
                if cfg.offsetsDemandingCall.ContainsKey offset then
                    let cilState', callSite, numberToDrop = executeSeparatedOpCode methodInterpreter cfg initialCilState
                    let createEdge (cilState' : cilState) dstVertex = CallEdge (srcVertex, dstVertex, callSite, cilState'.state, numberToDrop, ilInterpreter)
                    let currentTime, vertices, q, used = addEdgeAndRenewQueue createEdge d cfg (currentTime, vertices, q, used) cilState'
                    if not <| PriorityQueue.isEmpty q then bypass cfg q used vertices currentTime
                    else vertices
                else
                    let finishedStates, incompleteStates, erroredStates = ilInterpreter.ExecuteAllInstructionsForCFGEdges cfg initialCilState
                    // filtering out states, which have failed on the first instruction
                    let incompleteStates = List.filter (fun (cilState : cilState) -> currentIp cilState <> srcVertex.Ip) incompleteStates
                    let goodStates = finishedStates |> List.filter (fun (cilState : cilState) -> currentIp cilState = d.v)
                    srcVertex.AddErroredStates erroredStates

                    let createEdge (cilState' : cilState) dstVertex = StepEdge(d.srcVertex, dstVertex, cilState')
                    let currentTime, vertices, q, used = (goodStates @ incompleteStates) |> List.fold (addEdgeAndRenewQueue createEdge d cfg) (currentTime, vertices, q, used)
                    if not <| PriorityQueue.isEmpty q then bypass cfg q used vertices currentTime
                    else vertices
            let offset = block.entryPoint.Ip.Offset()
            let d0 = { u = block.entryPoint.Ip; srcVertex = block.entryPoint; uOut = cfg.dfsOut.[offset]
                       v = block.entryPoint.Ip; vOut = 0; minSCCs = 0; evaluationStack = initialState.evaluationStack
                       allocatedTypes = initialState.allocatedTypes; lengths = initialState.lengths; lowerBounds = initialState.lowerBounds }

            let q, used = updateQueue cfg block.entryPoint.Ip d0 (PriorityQueue.empty false, PersistentSet.empty)
            let vertices = PersistentDict.empty
                           |> PersistentDict.add (block.entryPoint.Ip, initialState.evaluationStack) block.entryPoint
                           |> PersistentDict.add (block.exitVertex.Ip, block.exitVertex.EvaluationStack) block.exitVertex
            let vertices = bypass cfg q used vertices initialState.currentTime
            vertices |> PersistentDict.values |> Seq.iter block.AddVertex

        let computeCFA (methodInterpreter : MethodInterpreter) (funcId: IFunctionIdentifier) : cfa =
            let methodBase = funcId.Method
            match alreadyComputedCFAs.ContainsKey methodBase with
            | true -> alreadyComputedCFAs.[methodBase]
            | _ ->
                let initialState = ExplorerBase.FormInitialStateWithoutStatics funcId
                assert(Option.isNone initialState.returnRegister)

                let cfg = CFG.build methodBase
                let cfa = createEmptyCFA cfg methodBase

                computeCFAForBlock methodInterpreter initialState cfa cfa.body
                alreadyComputedCFAs.[methodBase] <- cfa
                Logger.printLog Logger.Trace "Computed cfa: %O" cfa
                cfa

// Most probably won't be used in real testing
// Aimed to test composition and Interpreter--Searcher feature
type CFASearcher(maxBound) =
    inherit ForwardSearcher(maxBound) with
        override x.PickNext states =
            // 1) should append states to Queue
            // 2) should stop executing states and produce states with proper
            //    a) current time
            //    b) evaluationStack (including FRCS)

            let canBePropagated (s : cilState) =
                let conditions = [isIIEState; isUnhandledError; x.Used; isExecutable >> not]
                conditions |> List.fold (fun acc f -> acc || f s) false |> not

            let states = states |> Seq.filter canBePropagated
            match states with
            | Seq.Cons(x, _) -> Some x
            | Seq.Empty -> None

type EffectsFirstSearcher(maxBound) =
    inherit ForwardSearcher(maxBound)
    let effectsFirst (s1 : cilState) (s2 : cilState) =
        match s1, s2 with
        | _ when s1 = s2 -> 0
        | _ when List.length s1.ipStack > List.length s2.ipStack -> 1
        | _ when List.length s1.ipStack < List.length s2.ipStack -> -1
        | _ -> compare s1.ipStack s2.ipStack
    override x.PickNext all =
        let canBePropagated (s : cilState) =
            let conditions = [isIIEState; isUnhandledError; x.Used; isExecutable >> not]
            conditions |> List.fold (fun acc f -> acc || f s) false |> not

        let states = all |> Seq.filter canBePropagated

        match states with
        | Seq.Empty -> None
        | Seq.Cons(s, _) when x.ShouldStartExploringInIsolation (all, s) ->
            try
                let currentIp = currentIp s
                let m = currentMethod currentIp
                let stateForComposition = ExplorerBase.FormInitialStateWithoutStatics { methodBase = m } // TODO: #mbdo replace IFunctionIdentifier from stackFrame with MethodBase -- актуально? #do
                let cilStateForComposition = makeInitialState m stateForComposition
                Some cilStateForComposition
            with
            | :? InsufficientInformationException -> Some s
        | Seq.Cons(s, _) -> Some s
    abstract member ShouldStartExploringInIsolation: cilState seq * cilState -> bool
    default x.ShouldStartExploringInIsolation (_,_) = false

type AllMethodsExplorationSearcher(maxBound) =
    inherit EffectsFirstSearcher(maxBound)
    override x.ShouldStartExploringInIsolation (states, s) =
        match currentIp s with
        | Instruction(0, _) as ip when states |> Seq.filter (startingIpOf >> (=) ip) |> Seq.length = 0 -> true
        | _ -> false

type ParameterlessMethodsExplorationSearcher(maxBound) =
    inherit AllMethodsExplorationSearcher(maxBound)
    override x.ShouldStartExploringInIsolation(q, s) =
        base.ShouldStartExploringInIsolation(q, s) &&
            let m = let func = Memory.GetCurrentExploringFunction s.state in func.Method
            (m.IsConstructor || m.IsStatic) && m.GetParameters().Length = 0

type ExceptionsExplorationSearcher(maxBound) =
    inherit ParameterlessMethodsExplorationSearcher(maxBound)
    override x.ShouldStartExploringInIsolation(q, s) =
        base.ShouldStartExploringInIsolation(q, s) &&
            let m = let func = Memory.GetCurrentExploringFunction s.state in func.Method
            m.DeclaringType.IsSubclassOf(typeof<Exception>)
