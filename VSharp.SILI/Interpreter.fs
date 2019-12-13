namespace VSharp.Interpreter.IL

open System.Collections.Generic
open System
open System.Reflection
open System.Reflection.Emit
open InstructionsSet
open CFG
open VSharp
open VSharp.Core
open VSharp.Reflection

type public CodePortionInterpreter(ilInterpreter : ILInterpreter, codeLoc : ICodeLocation, cfg : cfgData, rv : int list) =
    inherit VSharp.Core.InterpreterBase<cilState>()
    let mutable result : cilState option = None
    let workingSet : List<cilState> = new List<_>()
    override x.MakeRecursiveState cilState =
        let methodId = ilInterpreter.MakeMethodIdentifier cfg.methodBase
        let ilCodePortion = ILCodePortion(cilState.targetVertex.Vertex(), cilState.recursiveVertices, methodId, cilState.state)
        {cilState with state = ilInterpreter.ReproduceEffect ilCodePortion cilState.state snd}

    member x.Invoke state this k =
        let getResultAndState = function
            | Some st -> st.functionResult |?? Nop, st.state
            | None -> Nop, Memory.EmptyState
        let interpret state curV targetV rvs =
            { makeEmptyState curV targetV state with recursiveVertices = rvs; this = this }
            |> x.Interpret
            |> getResultAndState |> k
        match codeLoc with
        | :? ILMethodMetadata ->
            Logger.info "Starting exploring method %O" codeLoc
            ilInterpreter.InitEntryPoint state cfg.methodBase.DeclaringType (fun state ->
            interpret state (Intermediate 0) destination.Return [])
        | :? ILCodePortion as ilcode ->
            let u = Intermediate ilcode.VertexNumber
            let rvs = ilcode.RecursiveVertices
            interpret state u u rvs
        | _ -> __notImplemented__()
    override x.MakeEpsilonState (ist : cilState) =
        let state = ist.state
        let pcForEpsilon = !! (conjunction state.pc)
        let state = { Memory.EmptyState with
                        pc = [pcForEpsilon]
                        frames = state.frames
                        stack = (fst Memory.EmptyState.stack, snd state.stack)
                    }
        makeEmptyState ist.currentVertex ist.currentVertex state
    override x.EvaluateOneStep cilState =
        assert (cilState.currentVertex <> destination.Return)
        let lastOffset = Seq.last cfg.sortedOffsets
        let u = cilState.currentVertex.Vertex ()
        let startingOffset = cfg.sortedOffsets.[u]
        let endOffset =
            if startingOffset = lastOffset then lastOffset + 1
            else cfg.sortedOffsets.[u + 1]
        let isOffsetOfCurrentVertex (offset : destination) = startingOffset <= offset.Vertex() && offset.Vertex() < endOffset
        let rec executeAllInstructions (offset : destination) cilState =
            let cilStates =
                ilInterpreter.ExecuteInstruction cfg (offset.Vertex()) cilState
                |> List.filter (fun (_, cilState : cilState) -> not cilState.HasException) //TODO: implement exceptions
            match cilStates with
            | list when List.forall (fst >> (=) destination.Return) list -> List.map (fun (_, state) -> { state with currentVertex = destination.Return}) list
            | (nextOffset, _)::xs as list when isOffsetOfCurrentVertex nextOffset
                                               && List.forall (fun (offset, _) -> offset = nextOffset && isOffsetOfCurrentVertex offset) xs ->
                List.collect ((<||) executeAllInstructions) list
            | list -> list |> List.map (fun (offset, cilSt) -> {cilSt with currentVertex = Intermediate (cfg.sortedOffsets.BinarySearch (offset.Vertex()))})
        executeAllInstructions (Intermediate startingOffset) cilState
        |> List.filter (fun st -> st.IsFinished || not (st.currentVertex.HasVertex() && List.contains (st.currentVertex.Vertex()) st.recursiveVertices))
    override x.IsRecursiveState cilState =
        let isHeadOfLoop (cfg : cfgData) v =
            let vTime = cfg.topologicalTimes.[v]
            cfg.reverseGraph.[v] |> Seq.exists (fun u -> cfg.topologicalTimes.[u] > vTime)
        match cilState.currentVertex with
        | Intermediate v ->
            isHeadOfLoop cfg v &&
            let rv = cilState.recursiveVertices
            let methodId = ilInterpreter.MakeMethodIdentifier cfg.methodBase
            let ilCodePortion = ILCodePortion(v, v :: rv, methodId, cilState.state)
            ilInterpreter.ShouldStopUnrolling ilCodePortion cilState.state
        | _ -> false
    override x.Add cilState = if cilState.currentVertex <> destination.Return then workingSet.Add cilState
    override x.ExploreInIsolation cilState =
        let u = cilState.currentVertex.Vertex()
        let rv = cilState.recursiveVertices
        let methodId = ilInterpreter.MakeMethodIdentifier cfg.methodBase
        let ilCodePortion = ILCodePortion(u, u :: rv, methodId, cilState.state)
        ilInterpreter.ReproduceEffect ilCodePortion cilState.state (fun (_, state) ->
        {cilState with state = state; recursiveVertices = u :: rv})
    override x.HasNextState () = workingSet.Count <> 0
    override x.FindSimilar cilState =
        let areCapableForMerge (st1 : cilState) (st2 : cilState) =
            st2.IsFinished
         || st1.IsFinished
         || st1.recursiveVertices = st2.recursiveVertices && st1.opStack = st2.opStack && st1.targetVertex = st2.targetVertex && st1.currentVertex = st2.currentVertex
        match Seq.tryFindIndex (areCapableForMerge cilState) workingSet with
        | None -> None
        | Some i -> let res = Some workingSet.[i]
                    workingSet.RemoveAt i
                    res
    override x.GetResultState () =
        match result with
        | None -> None
        | Some result -> Some ({ result with recursiveVertices = rv})
    override x.SetResultState newRes = result <- Some newRes
    override x.IsResultState cilState =
        match result with
        | None -> cilState.IsFinished
        | Some result -> cilState.IsFinished && result.targetVertex = cilState.targetVertex && result.opStack = cilState.opStack
    override x.PickNext () =
        let st = workingSet.[0]
        workingSet.RemoveAt 0
        st

and public ILInterpreter() as this =
    inherit VSharp.Core.ExplorerBase()
    do
        opcode2Function.[hashFunction OpCodes.Call]      <- zipWithOneOffset <| this.Call
        opcode2Function.[hashFunction OpCodes.Callvirt]  <- zipWithOneOffset <| this.CallVirt
        opcode2Function.[hashFunction OpCodes.Newobj]    <- zipWithOneOffset <| this.NewObj
        opcode2Function.[hashFunction OpCodes.Ldsfld]    <- zipWithOneOffset <| this.LdsFld false
        opcode2Function.[hashFunction OpCodes.Ldsflda]   <- zipWithOneOffset <| this.LdsFld true
        opcode2Function.[hashFunction OpCodes.Stsfld]    <- zipWithOneOffset <| this.StsFld
        opcode2Function.[hashFunction OpCodes.Ldfld]     <- zipWithOneOffset <| this.LdFld false
        opcode2Function.[hashFunction OpCodes.Ldflda]    <- zipWithOneOffset <| this.LdFld true
        opcode2Function.[hashFunction OpCodes.Stfld]     <- zipWithOneOffset <| this.StFld
        opcode2Function.[hashFunction OpCodes.Box]       <- zipWithOneOffset <| this.Box
        opcode2Function.[hashFunction OpCodes.Unbox]     <- zipWithOneOffset <| this.Unbox
        opcode2Function.[hashFunction OpCodes.Unbox_Any] <- zipWithOneOffset <| this.UnboxAny
    let cfgs = new Dictionary<ILMethodMetadata, cfgData>()
    let findCfg (ilmm : ILMethodMetadata) =
        Dict.getValueOrUpdate cfgs ilmm (fun () -> CFG.build ilmm.methodBase)

    member private x.Raise exptn (cilState : cilState) k =
        let exc, state = exptn cilState.state
        //TODO: exception handling
        k [Error exc, {cilState with state = state; exceptionFlag = Some exc}]

    member private x.NpeOrInvokeStatement (cilState : cilState) (this : term option) statement k =
        match this with
        | None -> statement cilState k
        | Some this ->
             BranchOnNull cilState this
                (x.Raise x.NullReferenceException)
                statement
                (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
                k
    member private x.ReduceMethodBaseCall (methodBase : MethodBase) cilState this (args : term list symbolicValue) k =
        let callMethodWithoutNRE (cilState : cilState) k =
            let state = cilState.state
            let k1 (term, state) = k [term, {cilState with state = state}]
            let fullMethodName = Reflection.GetFullMethodName methodBase
            let (&&&) = Microsoft.FSharp.Core.Operators.(&&&)
            if Map.containsKey fullMethodName Loader.internalImplementations then
                let thisAndArguments =
                    match args with
                    | Unspecified -> optCons [] this
                    | Specified args -> optCons args this
                internalCall Loader.internalImplementations.[fullMethodName] thisAndArguments state k1
            elif Map.containsKey fullMethodName Loader.concreteExternalImplementations then
                match args with
                | Specified parameters ->
                    let parameters' = optCons parameters this
                    let methodInfo = Loader.concreteExternalImplementations.[fullMethodName]
                    let methodId = x.MakeMethodIdentifier methodInfo
                    let invoke state k = x.Invoke methodId state this k
                    x.ReduceFunction state None (Specified parameters') methodId methodInfo invoke k1
                | _ -> internalfail "internal call with unspecified parameters!"
            elif int (methodBase.GetMethodImplementationFlags() &&& MethodImplAttributes.InternalCall) <> 0 then
                internalfailf "new extern method: %s" fullMethodName
            elif methodBase.GetMethodBody() <> null then
                x.ReduceConcreteCall methodBase state this args k1
            else
                internalfail "nonextern method without body!"
        x.NpeOrInvokeStatement cilState this callMethodWithoutNRE k

    member private x.CallMethodFromTermType (caller : locationBinding) (funcId : IFunctionIdentifier) (cilState : cilState) this parameters termType (calledMethod : MethodInfo) k =
        let t = termType |> Types.ToDotNetType
        let genericCalledMethod = if calledMethod.IsGenericMethod then calledMethod.GetGenericMethodDefinition() else calledMethod
        let genericMethodInfo =
            match genericCalledMethod.DeclaringType with
            | t1 when t1.IsInterface ->
                let createSignature (m : MethodInfo) =
                    m.GetParameters() |> Seq.map (fun p -> (p.ParameterType |> safeGenericTypeDefinition).FullName)
                    |> join ","
                let onlyLastName (m : MethodInfo) =
                    match m.Name.LastIndexOf('.') with
                    | i when i < 0 -> m.Name
                    | i -> m.Name.Substring(i + 1)
                let sign = createSignature genericCalledMethod
                let lastName = onlyLastName genericCalledMethod
                let methods =
                    match t with
                    | _ when t.IsArray -> t.GetMethods()
                    | _ -> t.GetInterfaceMap(t1).TargetMethods
                methods |> Seq.find (fun mi -> createSignature mi = sign && onlyLastName mi = lastName)
            | _ ->
                let (|||) = Microsoft.FSharp.Core.Operators.(|||)
                let allMethods = t.GetMethods(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
                Seq.find (fun (mi : MethodInfo) -> mi.GetBaseDefinition() = genericCalledMethod.GetBaseDefinition()) allMethods
        let targetMethod = if genericMethodInfo.IsGenericMethod then genericMethodInfo.MakeGenericMethod(calledMethod.GetGenericArguments()) else genericMethodInfo
        if targetMethod.IsAbstract
            then x.CallAbstract caller funcId cilState k
            else x.ReduceMethodBaseCall targetMethod cilState (Some this) parameters k

    member x.CallVirtualMethod (caller : locationBinding) (funcId : IFunctionIdentifier) cilState this parameters (methodInfo : MethodInfo) k =
        let baseType = BaseTypeOfRef this
        let sightType = SightTypeOfRef this
        let callForConcreteType typ state k =
            x.CallMethodFromTermType caller funcId state this parameters typ methodInfo k
        let tryToCallForBaseType cilState =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (API.Types.TypeIsRef baseType this &&& API.Types.TypeIsType baseType sightType, state))
                (callForConcreteType baseType)
                (x.CallAbstract caller funcId)
                (fun err -> (err, {cilState with exceptionFlag = Some err}) :: [])
        let tryToCallForSightType cilState =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (API.Types.TypeIsRef sightType this, state))
                (callForConcreteType sightType)
                tryToCallForBaseType
                (fun err -> (err, {cilState with exceptionFlag = Some err}) :: [])
        let sightDotNetType = Types.ToDotNetType sightType
        let baseDotNetType = Types.ToDotNetType baseType
        if sightDotNetType.IsInterface && baseDotNetType.IsInterface
            then x.CallAbstract caller funcId cilState k
            else tryToCallForSightType cilState k

    member private x.CallAbstract caller funcId (cilState : cilState) k =
        x.CallAbstractMethod caller funcId cilState.state (fun (result, state) -> k [result, {cilState with state = state}])

    member private x.Call (cfg : cfgData) offset (cilState : cilState) =
        let calledMethodBase = resolveMethodFromMetadata cfg (offset + OpCodes.Call.Size)
        let args, cilState = retrieveActualParameters calledMethodBase cilState
        let this, cilState = if not calledMethodBase.IsStatic then popStack cilState else None, cilState
        x.InitEntryPoint cilState.state calledMethodBase.DeclaringType (fun state ->
        x.ReduceMethodBaseCall calledMethodBase {cilState with state = state} this (Specified args) pushFunctionResults)
    member private x.CallVirt (cfg : cfgData) offset (cilState : cilState) =
        let ancestorMethodBase = resolveMethodFromMetadata cfg (offset + OpCodes.Callvirt.Size)
        x.InitEntryPoint cilState.state ancestorMethodBase.DeclaringType (fun state ->
        let args, cilState = retrieveActualParameters ancestorMethodBase cilState
        let this, cilState = popStack cilState |> mapfst Option.get
        let cilState = {cilState with state = state}
        if ancestorMethodBase.DeclaringType.IsSubclassOf typedefof<System.Delegate> then
            Lambdas.invokeDelegate "callvirt" args cilState this pushFunctionResults
        elif ancestorMethodBase.IsVirtual && not ancestorMethodBase.IsFinal then
            let ilmm = x.MakeMethodIdentifier ancestorMethodBase
            let methodInfo = ancestorMethodBase :?> MethodInfo
            x.CallVirtualMethod "callvirt" ilmm cilState this (Specified args) methodInfo pushFunctionResults
        else
            x.ReduceMethodBaseCall ancestorMethodBase cilState (Some this) (Specified args) pushFunctionResults)
    member private x.CreateDelegate typ (cilState : cilState) =
        match cilState.opStack with
        | methodPtr :: target :: stack ->
            let getMethodInfo methodPtr =
                match methodPtr.term with
                | Concrete(:? MethodInfo as mi, _) -> mi
                | _ -> __unreachable__()
            let invoke _ cilState args k =
                GuardedApply cilState methodPtr
                    (fun cilState methodPtr k ->
                        let methodInfo = getMethodInfo methodPtr
                        let invoke this cilState k = x.ReduceMethodBaseCall methodInfo cilState this args k
                        BranchOnNull cilState target
                            (invoke None)
                            (invoke (Some target))
                            (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
                            k)
                    k
            let explicitLambda : cilState list symbolicLambda = invoke
            let lambda = Lambdas.make explicitLambda typ
            let lambdaRefAndState = Memory.AllocateReferenceTypeInHeap cilState.state typ lambda
            pushResultOnStack {cilState with opStack = stack} lambdaRefAndState :: []
        | _ -> __notImplemented__()
    member private x.NewObj (cfg : cfgData) offset (cilState : cilState) =
        let constructorInfo = resolveMethodFromMetadata cfg (offset + OpCodes.Newobj.Size) :?> ConstructorInfo
        assert (constructorInfo.IsConstructor)
        let typ = constructorInfo.DeclaringType
        let constructedTermType = typ |> Types.FromDotNetType cilState.state
        let blockCase (cilState : cilState) =
            let args, cilState = retrieveActualParameters constructorInfo cilState
            let callConstructor cilState reference = x.ReduceMethodBaseCall constructorInfo cilState (Some reference) (Specified args)
            let referenceTypeCase (cilState : cilState) k =
                let ref, state = Memory.AllocateDefaultBlock cilState.state constructedTermType
                let k results = mapAndPushFunctionResultsk (fun (_, state) -> ref, state) results k
                callConstructor {cilState with state = state} ref k
            let valueTypeCase (cilState : cilState) k =
                let stackKey = SymbolicThisKey constructorInfo
                let freshValue = Memory.MakeDefaultBlock constructedTermType (HeapTopLevelStack stackKey, [])
                let state = Memory.NewScope cilState.state [(stackKey, Specified freshValue, constructedTermType)]
                let ref = Memory.ReferenceLocalVariable stackKey
                let k results =
                    let modifyResult (_, state) =
                        let value, state = Memory.Dereference state ref
                        value, Memory.PopStack state
                    mapAndPushFunctionResultsk modifyResult results k
                callConstructor {cilState with state = state} ref k
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Types.IsValueType constructedTermType, state))
                valueTypeCase
                referenceTypeCase
                (fun error -> {cilState with exceptionFlag = Some error} :: [])
                id
        let nonDelegateCase (cilState : cilState) =
            x.InitEntryPoint cilState.state typ (fun state ->
            if typ.IsArray && constructorInfo.GetMethodBody() = null
                then reduceArrayCreation typ constructorInfo {cilState with state = state} List.singleton
                else blockCase {cilState with state = state})
        if constructorInfo.DeclaringType.IsSubclassOf typedefof<System.Delegate>
            then x.CreateDelegate constructedTermType cilState
        elif constructorInfo.DeclaringType.IsSubclassOf typedefof<System.Exception>
            then
                let _, cilState = retrieveActualParameters constructorInfo cilState
                {cilState with opStack = MakeNullRef()::cilState.opStack} :: []
        else nonDelegateCase cilState
    member private x.LdsFld addressNeeded (cfg : cfgData) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Ldsfld.Size)
        assert (fieldInfo.IsStatic)
        x.InitEntryPoint cilState.state fieldInfo.DeclaringType (fun state ->
        let fieldType = fieldInfo.FieldType |> Types.FromDotNetType state
        let declaringTermType = fieldInfo.DeclaringType |> Types.FromDotNetType state
        let fullName = getFullNameOfField fieldInfo
        let address = Memory.ReferenceStaticField declaringTermType fullName fieldType
        let valueAndState =
            if addressNeeded then address, state
            else Memory.Dereference state address
        pushResultOnStack cilState valueAndState :: [])
    member private x.StsFld (cfg : cfgData) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Stsfld.Size)
        let state = cilState.state
        assert (fieldInfo.IsStatic)
        let fieldType = fieldInfo.FieldType |> Types.FromDotNetType state
        let declaringTermType = fieldInfo.DeclaringType |> Types.FromDotNetType state
        let fullName = getFullNameOfField fieldInfo
        let address = Memory.ReferenceStaticField declaringTermType fullName fieldType
        match cilState.opStack with
        | value :: stack ->
            x.InitEntryPoint state fieldInfo.DeclaringType (fun state ->
            let _, state = Memory.Mutate state address value
            {cilState with state = state; opStack = stack} :: [])
        | _ -> __notImplemented__()
    member private x.LdFld addressNeeded (cfg : cfgData) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Ldfld.Size)
        assert (not fieldInfo.IsStatic)
        match cilState.opStack with
        | target :: stack ->
            let loadWhenTargetIsNotNull (cilState : cilState) k =
                let state = cilState.state
                let k1 (value, state) = k [value, {cilState with state = state}]
                let fieldType = fieldInfo.FieldType |> Types.FromDotNetType state
                let fullName = getFullNameOfField fieldInfo
                match addressNeeded, IsStruct target with
                | false, true -> k1 (Memory.ReadBlockField target fullName fieldType, state)
                | false, false -> Memory.ReferenceField target fullName fieldType |> Memory.Dereference state |> k1
                | true, _ -> k1 (Memory.ReferenceField target fullName fieldType, state)
            x.NpeOrInvokeStatement {cilState with opStack = stack} (Some target) loadWhenTargetIsNotNull pushFunctionResults
        | _ -> __notImplemented__()
    member private x.StFld (cfg : cfgData) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Stfld.Size)
        assert (not fieldInfo.IsStatic)
        match cilState.opStack with
        | value :: targetRef :: stack ->
            let storeWhenTargetIsNotNull (cilState : cilState) k =
                let state = cilState.state
                let fieldType = fieldInfo.FieldType |> Types.FromDotNetType state
                let fullName = getFullNameOfField fieldInfo
                let address = Memory.ReferenceField targetRef fullName fieldType
                let value, state = castUnchecked fieldType value state id
                let state = Memory.Mutate state address value |> snd
                k [Nop, {cilState with state = state}]
            x.NpeOrInvokeStatement {cilState with opStack = stack} (Some targetRef) storeWhenTargetIsNotNull getCilStateFromResult
        | _ -> __notImplemented__()
    member private x.BoxNullable (t : Type) v (cilState : cilState) =
        let hasValueMethodInfo = t.GetMethod("get_HasValue")
        let hasValueCase (cilState : cilState) k =
            let valueMethodInfo = t.GetMethod("get_Value")
            let underlyingTermType = Nullable.GetUnderlyingType(t) |> Types.FromDotNetType cilState.state
            let allocateResults results = mapAndPushFunctionResultsk (fun (res, state) -> Memory.AllocateValueTypeInHeap state underlyingTermType res) results k
            x.ReduceMethodBaseCall valueMethodInfo cilState (Some v) (Specified []) allocateResults
        let boxNullable (hasValue, cilState) =
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (hasValue, state))
                hasValueCase
                (fun cilState k -> k [{cilState with opStack = MakeNullRef() :: cilState.opStack}])
                (fun error -> {cilState with exceptionFlag = Some error} :: [])
        x.ReduceMethodBaseCall hasValueMethodInfo cilState (Some v) (Specified []) (fun hasValueResults ->
        Cps.List.mapk boxNullable hasValueResults List.concat)

    member private x.Box (cfg : cfgData) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Box.Size)
        let termType = Types.FromDotNetType cilState.state t
        match cilState.opStack with
        | v :: stack ->
            let boxValueType (cilState : cilState) =
                let cilState' = {cilState with opStack = stack}
                StatedConditionalExecutionCIL cilState'
                    (fun state k -> k (Types.TypeIsNullable termType, state))
                    (fun cilState k -> x.BoxNullable t v cilState |> k)
                    (fun cilState k -> allocateValueTypeInHeap v cilState |> k)
                    (fun err -> {cilState with exceptionFlag = Some err} :: [])
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Types.IsValueType termType, state))
                boxValueType
                (fun cilState k -> k [cilState])
                (fun err -> {cilState with exceptionFlag = Some err} :: [])
                id
        | _ -> __notImplemented__()
    member private x.UnboxCommon (op : OpCode) handleReferenceType handleRestResults (cfg : cfgData) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + op.Size)
        Logger.trace "UnboxCommon %O" t
        let termType = Types.FromDotNetType cilState.state t
        let InvalidCastException state = RuntimeExceptions.InvalidCastException state id
        match cilState.opStack with
        | _ :: _ when t.IsGenericParameter -> __notImplemented__() //TODO: Nullable.GetUnderlyingType for generics
        | obj :: stack ->
            assert(IsReference obj)
            let nullCase (cilState : cilState) =
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.TypeIsNullable termType, state))
                    (fun cilState k ->
                        let address, state = Memory.AllocateDefaultBlock cilState.state termType
                        k [handleRestResults(address, {cilState with state = state})])
                    (x.Raise x.NullReferenceException)
                    (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
            let canCastValueTypeToNullableTargetCase (cilState : cilState) =
                let underlyingTypeOfNullableT = Nullable.GetUnderlyingType(t)
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.RefIsType obj (Types.FromDotNetType state underlyingTypeOfNullableT), state))
                    (fun cilState k ->
                        let value, _ = Memory.Dereference cilState.state obj
                        let address, state = Memory.AllocateDefaultBlock cilState.state termType
                        let nullableConstructor = t.GetConstructor([| underlyingTypeOfNullableT |])
                        let modifyResults results = Cps.List.map (fun (_, cilState) -> handleRestResults (address, cilState)) results k
                        x.ReduceMethodBaseCall nullableConstructor {cilState with state = state} (Some address) (Specified [value]) modifyResults)
                    (x.Raise InvalidCastException)
                    (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
            let canCastValueTypeToTargetCase (cilState : cilState) =
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.TypeIsNullable termType, state))
                    canCastValueTypeToNullableTargetCase
                    (fun cilState k -> k [handleRestResults(castUnchecked termType obj cilState.state fst, cilState)])
                    (fun error -> [error, {cilState with exceptionFlag = Some error}])
            let valueTypeCase (cilState : cilState) =
                Logger.trace "Unbox.any: value type case %O [%O]" obj (TypeOf obj)
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.CanCast obj termType, state))
                    canCastValueTypeToTargetCase
                    (x.Raise InvalidCastException)
                    (fun error -> [error, {cilState with exceptionFlag = Some error}])
            let nonNullCase (cilState : cilState) =
                let SystemValueType = Types.FromDotNetType cilState.state typedefof<System.ValueType>
                StatedConditionalExecutionCIL cilState
                    (fun state k -> k (Types.RefIsType obj SystemValueType, state))
                    valueTypeCase
                    (handleReferenceType obj termType)
                    (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
            BranchOnNull {cilState with opStack = stack} obj
                nullCase
                nonNullCase
                (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
                pushFunctionResults
        | _ -> __notImplemented__()
    member private x.Unbox (cfg : cfgData) offset (cilState : cilState) =
        let InvalidCastException state = RuntimeExceptions.InvalidCastException state id
        x.UnboxCommon OpCodes.Unbox (fun _ _ -> x.Raise InvalidCastException) id cfg offset cilState
    member private x.UnboxAny (cfg : cfgData) offset (cilState : cilState) =
        let InvalidCastException state = RuntimeExceptions.InvalidCastException state id
        let handleReferenceTypeResults obj termType cilState =
            Logger.trace "Unbox.any: reference type case %O [%O]" obj  (TypeOf obj)
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Types.CanCast obj termType, state))
                (fun cilState k -> k [castUnchecked termType obj cilState.state fst, cilState])
                (x.Raise InvalidCastException)
                (fun error -> (error, {cilState with exceptionFlag = Some error}) :: [])
        let handleRestResults (address, cilState : cilState) = Memory.Dereference cilState.state address |> fst, cilState
        x.UnboxCommon OpCodes.Unbox_Any handleReferenceTypeResults handleRestResults cfg offset cilState

    // -------------------------------- ExplorerBase operations -------------------------------------
    override x.Invoke codeLoc state this k =
        match codeLoc with
        | :? ILMethodMetadata as ilmm ->
            let interpreter = new CodePortionInterpreter(x, ilmm, findCfg ilmm, [])
            interpreter.Invoke state this k
        | :? ILCodePortion as ilcode ->
            let ilmm = ilcode.FuncId :?> ILMethodMetadata
            let interpreter = new CodePortionInterpreter(x, ilcode, findCfg ilmm, ilcode.RecursiveVertices)
            interpreter.Invoke state this k
        | _ -> internalfail "unhandled ICodeLocation instance"
    override x.FormInitialState funcId state this =
        match funcId with
        | :? ILMethodMetadata as ilmm ->
            let methodId = x.MakeMethodIdentifier ilmm.methodBase
            x.InitEntryPoint state ilmm.methodBase.DeclaringType (fun state ->
            x.ReduceFunctionSignature methodId state ilmm.methodBase this Unspecified id)
        | _ -> __notImplemented__()
    override x.MakeMethodIdentifier m = { methodBase = m } :> IMethodIdentifier
    member x.ExecuteInstruction (cfg : cfgData) (offset : int) (cilState : cilState) =
        let opcode = Instruction.parseInstruction cfg.ilBytes offset
        Logger.trace "Executing instruction %O of %O [%O]" opcode cfg.methodBase cfg.methodBase.DeclaringType
        let nextTargets = Instruction.findNextInstructionOffsetAndEdges opcode cfg.ilBytes offset
        let newOffsets =
            match nextTargets with
            | Choice1Of2 nextInstruction -> [Intermediate nextInstruction]
            | Choice2Of2 [] -> [Return]
            | Choice2Of2 targets -> targets |> List.map Intermediate
        let k = API.Enter opcode cilState.state id
        let newSts = opcode2Function.[hashFunction opcode] cfg offset newOffsets cilState
        k ()
        newSts
