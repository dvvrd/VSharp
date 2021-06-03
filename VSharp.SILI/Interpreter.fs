namespace VSharp.Interpreter.IL

open System
open System.Reflection
open System.Reflection.Emit
open FSharpx.Collections
open InstructionsSet
open CilStateOperations
open VSharp
open VSharp.Core
open ipOperations
open Instruction

type cfg = CFG.cfgData

type public MethodInterpreter(searcher : ForwardSearcher (*ilInterpreter : ILInterpreter, funcId : IFunctionIdentifier, cfg : cfg*)) =
    inherit ExplorerBase()
    member x.GetResults initialState (q : IndexedQueue) =
        let (|CilStateWithIIE|_|) (cilState : cilState) = cilState.iie
        let isStartingDescender (s : cilState) = s.startingIP = initialState.startingIP
        let allStates = List.filter isStartingDescender (q.GetStates())
        let iieStates, nonIIEstates = List.partition isIIEState allStates
        let isFinished (s : cilState) = s.ipStack = [Exit <| currentMethod initialState.startingIP]
        let finishedStates = List.filter isFinished nonIIEstates
        let isValid (cilState : cilState) =
           match IsValid cilState.state with
           | SolverInteraction.SmtUnsat _ -> false
           | _ -> true
        let validStates = List.filter isValid finishedStates
//        let printInfoForDebug () =
//            let allStatesInQueue = q.GetStates()
//            Logger.info "No states were obtained. Most likely such a situation is a bug. Check it!"
//            Logger.info "Indexed queue size = %d\n" (List.length allStatesInQueue)
//            List.iteri (fun i -> dump >> Logger.info "Queue.[%d]:\n%s\n" i) allStatesInQueue
//            true
        match iieStates with // TODO: write error states? #do
        | CilStateWithIIE iie :: _ -> raise iie
        | _ :: _ -> __unreachable__()
        | _ when validStates = [] ->
//            assert(printInfoForDebug())
            internalfailf "No states were obtained. Most likely such a situation is a bug. Check it!"
        | _ -> validStates

    member x.Interpret (mainId : IFunctionIdentifier) (initialState : cilState) =
        let q = IndexedQueue()
        q.Add initialState

        let hasAnyProgress (s : cilState) = [s.startingIP] <> s.ipStack
        let isEffectFor currentIp (s : cilState) = hasAnyProgress s && startingIpOf s = currentIp
        let step s =
            let states = List.filter (isEffectFor (currentIp s)) (q.GetStates() @ [s]) // TODO: need to add to tail? #do
            match states with
            | [] ->
                let goodStates, incompleteStates, errors = ILInterpreter(x).ExecuteOnlyOneInstruction s
                goodStates @ incompleteStates @ errors
            | _ -> List.map (compose s) states |> List.concat
            |> List.iter q.Add

        let iter () = // TODO: recursion! #do
            let mutable b = true
            while b do
                match (searcher :> INewSearcher).ChooseAction (q.GetStates(), [], [], mainId) with
                | Stop -> b <- false
                | GoForward s ->
                    q.Remove s
                    step s
                | _ -> __unreachable__()
        iter()
        x.GetResults initialState q

//    override x.AnswerPobs typ initialState k = __notImplemented__()
    override x.Invoke funcId initialState k =
        let cilStates = x.InitializeStatics initialState funcId.Method.DeclaringType List.singleton
        assert(List.length cilStates = 1)
        let cilState = List.head cilStates
        let results = x.Interpret funcId cilState
        let printResults (cilStates : cilState list) =
            let states = List.fold (fun acc (cilState : cilState) -> acc + Memory.Dump cilState.state + "\n") "" cilStates
            let fullMethodName = Reflection.getFullMethodName funcId.Method
            Logger.info "For method %O got %i states :\n%s" fullMethodName (List.length cilStates) states
        printResults results
        k results

    override x.MakeMethodIdentifier m = { methodBase = m } :> IMethodIdentifier

and public ILInterpreter(methodInterpreter : ExplorerBase) as this =
    do
        opcode2Function.[hashFunction OpCodes.Call]           <- this.Call
        opcode2Function.[hashFunction OpCodes.Callvirt]       <- this.CallVirt
        opcode2Function.[hashFunction OpCodes.Newobj]         <- this.NewObj
        opcode2Function.[hashFunction OpCodes.Ldsfld]         <- this.LdsFld false
        opcode2Function.[hashFunction OpCodes.Ldsflda]        <- this.LdsFld true
        opcode2Function.[hashFunction OpCodes.Stsfld]         <- this.StsFld
        opcode2Function.[hashFunction OpCodes.Ldfld]          <- zipWithOneOffset <| this.LdFld false
        opcode2Function.[hashFunction OpCodes.Ldflda]         <- zipWithOneOffset <| this.LdFld true
        opcode2Function.[hashFunction OpCodes.Stfld]          <- zipWithOneOffset <| this.StFld
        opcode2Function.[hashFunction OpCodes.Ldelem]         <- zipWithOneOffset <| this.LdElem
        opcode2Function.[hashFunction OpCodes.Ldelema]        <- zipWithOneOffset <| this.LdElema
        opcode2Function.[hashFunction OpCodes.Ldelem_I1]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int8Type
        opcode2Function.[hashFunction OpCodes.Ldelem_I2]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int16Type
        opcode2Function.[hashFunction OpCodes.Ldelem_I4]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Ldelem_I8]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Ldelem_R4]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.float32Type
        opcode2Function.[hashFunction OpCodes.Ldelem_R8]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.float64Type
        opcode2Function.[hashFunction OpCodes.Ldelem_U1]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.uint8Type
        opcode2Function.[hashFunction OpCodes.Ldelem_U2]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.uint16Type
        opcode2Function.[hashFunction OpCodes.Ldelem_U4]      <- zipWithOneOffset <| fun _ _ -> this.LdElemTyp TypeUtils.uint32Type
        opcode2Function.[hashFunction OpCodes.Ldelem_Ref]     <- zipWithOneOffset <| fun _ _ -> this.LdElemRef
        opcode2Function.[hashFunction OpCodes.Stelem]         <- zipWithOneOffset <| this.StElem
        opcode2Function.[hashFunction OpCodes.Stelem_I1]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int8Type
        opcode2Function.[hashFunction OpCodes.Stelem_I2]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int16Type
        opcode2Function.[hashFunction OpCodes.Stelem_I4]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Stelem_I8]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Stelem_R4]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.float32Type
        opcode2Function.[hashFunction OpCodes.Stelem_R8]      <- zipWithOneOffset <| fun _ _ -> this.StElemTyp TypeUtils.float64Type
        opcode2Function.[hashFunction OpCodes.Stelem_Ref]     <- zipWithOneOffset <| fun _ _ -> this.StElemRef
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I1]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int8Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I2]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int16Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I4]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I8]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I]     <- zipWithOneOffset <| fun _ _ -> convi // TODO: overflow? #do
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U1]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint8Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U2]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint16Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U4]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U8]    <- zipWithOneOffset <| fun _ _ -> this.ConvOvf TypeUtils.uint64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U]     <- zipWithOneOffset <| fun _ _ -> convu // TODO: overflow? #do
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I1_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int8Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I2_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int16Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I4_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.int32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I8_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint64Type TypeUtils.int64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_I_Un]  <- zipWithOneOffset <| fun _ _ -> convi // TODO: overflow? #do
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U1_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint8Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U2_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint16Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U4_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint32Type TypeUtils.uint32Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U8_Un] <- zipWithOneOffset <| fun _ _ -> this.ConvOvfUn TypeUtils.uint64Type TypeUtils.uint64Type
        opcode2Function.[hashFunction OpCodes.Conv_Ovf_U_Un]  <- zipWithOneOffset <| fun _ _ -> convu // TODO: overflow? #do
        opcode2Function.[hashFunction OpCodes.Castclass]      <- zipWithOneOffset <| this.CastClass
        opcode2Function.[hashFunction OpCodes.Ldlen]          <- zipWithOneOffset <| fun _ _ -> this.LdLen
        opcode2Function.[hashFunction OpCodes.Ldvirtftn]      <- zipWithOneOffset <| this.LdVirtFtn
        opcode2Function.[hashFunction OpCodes.Box]            <- zipWithOneOffset <| this.Box
        opcode2Function.[hashFunction OpCodes.Unbox]          <- zipWithOneOffset <| this.Unbox
        opcode2Function.[hashFunction OpCodes.Unbox_Any]      <- zipWithOneOffset <| this.UnboxAny
        opcode2Function.[hashFunction OpCodes.Add_Ovf_Un]     <- zipWithOneOffset <| fun _ _ -> this.Add_ovf_un
        opcode2Function.[hashFunction OpCodes.Sub_Ovf_Un]     <- zipWithOneOffset <| fun _ _ -> this.Sub_ovf_un
        opcode2Function.[hashFunction OpCodes.Mul_Ovf_Un]     <- zipWithOneOffset <| fun _ _ -> this.Mul_ovf_un
        opcode2Function.[hashFunction OpCodes.Add_Ovf]        <- zipWithOneOffset <| fun _ _ -> this.Add_ovf
        opcode2Function.[hashFunction OpCodes.Sub_Ovf]        <- zipWithOneOffset <| fun _ _ -> this.Sub_ovf
        opcode2Function.[hashFunction OpCodes.Mul_Ovf]        <- zipWithOneOffset <| fun _ _ -> this.Mul_ovf
        opcode2Function.[hashFunction OpCodes.Div]            <- zipWithOneOffset <| fun _ _ -> this.Div
        opcode2Function.[hashFunction OpCodes.Div_Un]         <- zipWithOneOffset <| fun _ _ -> this.DivUn
        opcode2Function.[hashFunction OpCodes.Rem]            <- zipWithOneOffset <| fun _ _ -> this.Rem
        opcode2Function.[hashFunction OpCodes.Rem_Un]         <- zipWithOneOffset <| fun _ _ -> this.RemUn
        opcode2Function.[hashFunction OpCodes.Newarr]         <- zipWithOneOffset <| this.Newarr
        opcode2Function.[hashFunction OpCodes.Throw]          <- this.Throw

    let internalCILImplementations : Map<string, (cilState -> term option -> term list -> cilState list)> =
        Map.ofList [
            "System.Int32 System.Array.GetLength(this, System.Int32)", this.CommonGetArrayLength
            "System.Int32 System.Array.GetLowerBound(this, System.Int32)", this.GetArrayLowerBound
            "System.Void System.Runtime.CompilerServices.RuntimeHelpers.InitializeArray(System.Array, System.RuntimeFieldHandle)", this.CommonInitializeArray
            "System.Void System.String.FillStringChecked(System.String, System.Int32, System.String)", this.FillStringChecked
        ]

    member private x.Raise createException (cilState : cilState) k =
        let statesWithCreatedExceptions = createException cilState
        k statesWithCreatedExceptions

    member private x.MultiDimensionalAccessArray accessor (cilState : cilState) upperBound (index : term list) k = __notImplemented__()
//        let checkArrayBounds upperBound x =
//            let lowerBound = Concrete 0 Types.TLength
//            let notTooSmall = Arithmetics.(>>=) x lowerBound
//            let notTooLarge = Arithmetics.(<<) x upperBound
//            notTooSmall &&& notTooLarge
//        StatedConditionalExecutionAppendResultsCIL cilState
//            (fun state k -> k (checkArrayBounds upperBound index, state))
//            accessor
//            (x.Raise x.IndexOutOfRangeException)
//            k

    member private x.AccessArray accessor (cilState : cilState) upperBound index k =
        let checkArrayBounds upperBound x =
            let lowerBound = Concrete 0 Types.TLength
            let notTooSmall = Arithmetics.(>>=) x lowerBound
            let notTooLarge = Arithmetics.(<<) x upperBound
            notTooSmall &&& notTooLarge
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (checkArrayBounds upperBound index, state))
            accessor
            (x.Raise x.IndexOutOfRangeException)
            k

    member private x.AccessArrayDimension accessor (cilState : cilState) (this : term) (dimension : term) =
        let upperBound = Memory.ArrayRank cilState.state this
        x.AccessArray (accessor this dimension) cilState upperBound dimension id

    member private x.CommonGetArrayLength (cilState : cilState) thisOption args =
        match args with
        | dimensionsKey :: [] ->
            let arrayLengthByDimension arrayRef index cilState (k : cilState list -> 'a) =
                cilState |> push (Memory.ArrayLengthByDimension cilState.state arrayRef index) |> List.singleton |> k
            x.AccessArrayDimension arrayLengthByDimension cilState (Option.get thisOption) dimensionsKey
        | _ -> internalfail "unexpected number of arguments"

    member private x.GetArrayLowerBound (cilState : cilState) (this : term option) args =
        match args with
        | dimension :: [] ->
            let arrayLowerBoundByDimension arrayRef index (cilState : cilState) k =
                cilState |> push (Memory.ArrayLowerBoundByDimension cilState.state arrayRef index) |> List.singleton |> k
            x.AccessArrayDimension arrayLowerBoundByDimension cilState (Option.get this) dimension
        | _ -> internalfail "unexpected number of arguments"

//    member private x.SetArrayElement (cilState : cilState) (this : term option) args =
//        match this with
//        | Some arrayRef ->
//            let setElement
//        | None -> __unreachable__()

    member private x.NpeOrInvokeStatementCIL (cilState : cilState) (this : term) statement (k : cilState list -> 'a) =
         StatedConditionalExecutionCIL cilState
            (fun state k -> k (IsNullReference this, state))
            (x.Raise x.NullReferenceException)
            statement
            k

    member private x.CommonInitializeArray (cilState : cilState) _ (args : term list) =
        match args with
        | arrayRef :: handleTerm :: [] ->
            x.NpeOrInvokeStatementCIL cilState arrayRef (fun cilState k ->
            x.NpeOrInvokeStatementCIL cilState handleTerm (fun cilState k ->
            let results : state list = VSharp.System.Runtime_CompilerServices_RuntimeHelpers.InitializeArray cilState.state arrayRef handleTerm
            let cilResults = List.map (fun state -> withState state cilState) results
            k cilResults) k) id
        | _ -> internalfail "unexpected number of arguments"

    member private x.FillStringChecked (cilState : cilState) _ (args : term list) =
        assert(List.length args = 3)
        let state = cilState.state
        let dest, destPos, src = args.[0], args.[1], args.[2]
        let srcPos = MakeNumber 0
        let srcLength = Memory.StringLength state src
        let destLength = Memory.StringLength state dest
        let (<<=) = Arithmetics.(<<=)
        let check = srcLength <<= (Arithmetics.Sub destLength destPos)
        let copy (cilState : cilState) k =
            let state' = Memory.CopyStringArray cilState.state src srcPos dest destPos srcLength
            withState state' cilState |> List.singleton |> k
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (check, state))
            copy
            (x.Raise x.IndexOutOfRangeException)
            id

    member private x.IsNotImplementedIntrinsic (methodBase : MethodBase) = // TODO: do better #do
        let implementedIntrinsics =
            typeof<IntPtr>.GetMethods(Reflection.allBindingFlags)
            |> Array.map (fun mi -> mi :> MethodBase)
        let isIntrinsic =
            let intrinsicAttr = "System.Runtime.CompilerServices.IntrinsicAttribute"
            methodBase.CustomAttributes |> Seq.exists (fun m -> m.AttributeType.ToString() = intrinsicAttr)
        isIntrinsic && (Array.contains methodBase implementedIntrinsics |> not)

    member private x.InlineMethodBaseCallIfNeeded (methodBase : MethodBase) (cilState : cilState) (k : cilState list -> 'a) =
        let canInline =
            match currentIp cilState with
            | Instruction(0, m) -> m = methodBase
            | _ -> false
        // because we have correspondence between ips and frames
        assert(canInline)
        let state = cilState.state
        let thisOption = if methodBase.IsStatic then None else Some <| Memory.ReadThis state methodBase
        let state =
            match thisOption with
            | Some this ->
                let thisType = TypeOf this
                if Types.IsValueType thisType && methodBase.IsConstructor then
                    let newThis = Memory.DefaultOf thisType
                    let states = Memory.WriteSafe state this newThis
                    assert(List.length states = 1)
                    List.head states
                else state
            | None -> state
        let cilState = withState state cilState
        let fullyGenericMethod, genericArgs, _ = Reflection.generalizeMethodBase methodBase
        let wrapType arg = Concrete arg (Types.FromDotNetType typeof<Type>)
        let typeArgs = genericArgs |> Seq.map wrapType |> List.ofSeq
        let termArgs = methodBase.GetParameters() |> Seq.map (Memory.ReadArgument state) |> List.ofSeq
        let args = typeArgs @ termArgs
//        let fullGenericMethodName = Reflection.getFullMethodName methodBase
        let fullGenericMethodName = Reflection.getFullMethodName fullyGenericMethod
        if methodBase.Name = "get_CategoryLevel1Index" then ()
        let (&&&) = Microsoft.FSharp.Core.Operators.(&&&)
        let moveIpToExit (cilState : cilState) = cilState |> setCurrentIp (Exit methodBase)
        if Map.containsKey fullGenericMethodName internalCILImplementations then
            // TODO: generalize method for internal call
            // TODO: we may generalize only name! Can we generalize arguments? #do
            (internalCILImplementations.[fullGenericMethodName] cilState thisOption args) |> (List.map moveIpToExit >> k)
        elif Map.containsKey fullGenericMethodName Loader.internalImplementations then
            let thisAndArguments = optCons args thisOption
            internalCall Loader.internalImplementations.[fullGenericMethodName] thisAndArguments state (List.map (changeState cilState >> moveIpToExit) >> k)
        elif Map.containsKey fullGenericMethodName Loader.concreteExternalImplementations then
            // TODO: check that all parameters were specified
            let methodInfo = Loader.concreteExternalImplementations.[fullGenericMethodName]
            let thisOption, args =
                match thisOption, methodInfo.IsStatic with
                | Some this, true -> None, this :: args
                | None, false -> internalfail "Calling non-static concrete implementation for static method"
                | _ -> thisOption, args
            let state = Memory.PopFrame state
            let methodId = methodInterpreter.MakeMethodIdentifier methodInfo
            let cilState = ExplorerBase.ReduceFunctionSignature state methodId thisOption (Some args) id |> changeState cilState
            let cilStates = methodInterpreter.InitializeStatics cilState methodInfo.DeclaringType (setCurrentIp (instruction methodInfo 0) >> List.singleton)
            // NOTE: callsite of cilState is explicitly untouched
            k cilStates
        elif fullGenericMethodName.Contains "System.Array.Set(" then // TODO: do better #do
            (internalCILImplementations.[fullGenericMethodName] cilState thisOption args) |> (List.map moveIpToExit >> k)
        elif int (methodBase.GetMethodImplementationFlags() &&& MethodImplAttributes.InternalCall) <> 0 || (methodBase.Attributes.HasFlag(MethodAttributes.PinvokeImpl)) then
            internalfailf "new extern method: %s" fullGenericMethodName
        elif x.IsNotImplementedIntrinsic methodBase then
            internalfailf "new intrinsic method: %s" fullGenericMethodName
        elif methodBase.GetMethodBody() <> null then
            cilState |> List.singleton |> k
        else
            __insufficientInformation__ "non-extern method %s without body!" (Reflection.getFullMethodName methodBase) // TODO: hack #do

     // TODO: think about generalization #do
    member x.CallMethodFromTermType (cilState : cilState) (*this parameters *) termType (calledMethod : MethodInfo) (k : cilState list -> 'a) =
        let t = termType |> Types.ToDotNetType
        let genericCalledMethod = if calledMethod.IsGenericMethod then calledMethod.GetGenericMethodDefinition() else calledMethod
        let genericMethodInfo =
            match genericCalledMethod.DeclaringType with
            | t1 when t1.IsInterface ->
                let createSignature (m : MethodInfo) =
                    m.GetParameters()
                    |> Seq.map (fun p -> p.ParameterType |> safeGenericTypeDefinition |> Reflection.getFullTypeName)
                    |> join ","
                let onlyLastName (m : MethodInfo) =
                    match m.Name.LastIndexOf('.') with
                    | i when i < 0 -> m.Name
                    | i -> m.Name.Substring(i + 1)
                let sign = createSignature genericCalledMethod
                let lastName = onlyLastName genericCalledMethod
                let methods =
                    match t with
                    | _ when t.IsArray ->
                        let methodsFromSystemArray =
                            Array.append
                                (System.Type.GetType("System.SZArrayHelper").GetMethods(Reflection.allBindingFlags))
                                (typeof<System.Array>.GetMethods(Reflection.allBindingFlags))
                        let f (m : MethodInfo) = // TODO: hack #do
                            if m.IsGenericMethod && Array.length (m.GetGenericArguments()) = 1 then m.MakeGenericMethod(t.GetElementType()) else m
                        let concreteMethodsFromSystemArray = Array.map f methodsFromSystemArray
//                            methodsFromSystemArray |> Array.map (fun m -> Reflection.concretizeMethodBase m f :?> MethodInfo)
                        Array.append (t.GetMethods(Reflection.allBindingFlags)) concreteMethodsFromSystemArray
                    | _ -> t.GetInterfaceMap(t1).TargetMethods
                methods |> Seq.find (fun mi -> createSignature mi = sign && onlyLastName mi = lastName)
            | _ ->
                let (|||) = Microsoft.FSharp.Core.Operators.(|||)
                let allMethods = t.GetMethods(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
                Seq.find (fun (mi : MethodInfo) -> mi.GetBaseDefinition() = genericCalledMethod.GetBaseDefinition()) allMethods
        let targetMethod = if genericMethodInfo.IsGenericMethodDefinition then genericMethodInfo.MakeGenericMethod(calledMethod.GetGenericArguments()) else genericMethodInfo
        if targetMethod.IsAbstract
            then x.CallAbstract (methodInterpreter.MakeMethodIdentifier targetMethod) cilState k
            else
                // Getting this and arguments values by old keys
                let this = Memory.ReadThis cilState.state calledMethod
                let args = calledMethod.GetParameters() |> Seq.map (Memory.ReadArgument cilState.state) |> List.ofSeq
                // Popping frame created for ancestor calledMethod
                let cilState = popFrameOf cilState
                // Creating valid frame with stackKeys corresponding to actual targetMethod
                methodInterpreter.ReduceFunctionSignatureCIL cilState targetMethod (Some this) (Some args) (fun cilState ->
                x.InlineMethodBaseCallIfNeeded targetMethod cilState k)

    member x.CallVirtualMethod (ancestorMethod : MethodInfo) (cilState : cilState) (k : cilState list -> 'a) =
        let methodId = methodInterpreter.MakeMethodIdentifier ancestorMethod
        let this = Memory.ReadThis cilState.state ancestorMethod
        let callVirtual (cilState : cilState) this k =
            let baseType = MostConcreteTypeOfHeapRef cilState.state this
            let callForConcreteType typ state k = // TODO: initialize statics? #do
                x.CallMethodFromTermType state typ ancestorMethod k
            let tryToCallForBaseType (cilState : cilState) (k : cilState list -> 'a) =
                StatedConditionalExecutionAppendResultsCIL cilState
                    (fun state k -> k (API.Types.TypeIsRef state baseType this, state)) // TODO: may this be Ref to ValueType? #do
                    (callForConcreteType baseType)
                    (x.CallAbstract methodId)
                    k
            let baseDotNetType = Types.ToDotNetType baseType
            if baseDotNetType.IsInterface
                then x.CallAbstract methodId cilState k
                else tryToCallForBaseType cilState k
        GuardedApplyCIL cilState this callVirtual k

    member x.CallAbstract funcId cilState k =
        methodInterpreter.CallAbstractMethod funcId cilState k

    member private x.ConvOvf targetType (cilState : cilState) =
        let supersetsOf =
            PersistentDict.ofSeq [
                TypeUtils.int8Type,    [|TypeUtils.int8Type; TypeUtils.int16Type; TypeUtils.int32Type; TypeUtils.int64Type|]
                TypeUtils.int16Type,   [|TypeUtils.int16Type; TypeUtils.int32Type; TypeUtils.int64Type|]
                TypeUtils.int32Type,   [|TypeUtils.int32Type; TypeUtils.int64Type|]
                TypeUtils.int64Type,   [|TypeUtils.int64Type|]
                TypeUtils.uint8Type,   [|TypeUtils.uint8Type; TypeUtils.uint16Type; TypeUtils.uint32Type; TypeUtils.uint64Type|]
                TypeUtils.uint16Type,  [|TypeUtils.uint16Type; TypeUtils.uint32Type; TypeUtils.uint64Type|]
                TypeUtils.uint32Type,  [|TypeUtils.uint32Type; TypeUtils.uint64Type|]
                TypeUtils.uint64Type,  [|TypeUtils.uint64Type|]
                TypeUtils.float32Type, [|TypeUtils.float32Type; TypeUtils.float64Type|]
                TypeUtils.float64Type, [|TypeUtils.float64Type|] ]
        let isSubset leftTyp rightTyp = Array.contains rightTyp supersetsOf.[leftTyp]
        let minMaxOf = // TODO: implement big numbers, instead of double #hack
            PersistentDict.ofSeq [
                TypeUtils.int8Type,    (System.SByte.MinValue  |> double, System.SByte.MaxValue  |> double)
                TypeUtils.int16Type,   (System.Int16.MinValue  |> double, System.Int16.MaxValue  |> double)
                TypeUtils.int32Type,   (System.Int32.MinValue  |> double, System.Int32.MaxValue  |> double)
                TypeUtils.int64Type,   (System.Int64.MinValue  |> double, System.Int64.MaxValue  |> double)
                TypeUtils.uint8Type,   (System.Byte.MinValue   |> double, System.Byte.MaxValue   |> double)
                TypeUtils.uint16Type,  (System.UInt16.MinValue |> double, System.UInt16.MaxValue |> double)
                TypeUtils.uint32Type,  (System.UInt32.MinValue |> double, System.UInt32.MaxValue |> double)
                TypeUtils.uint64Type,  (System.UInt64.MinValue |> double, System.UInt64.MaxValue |> double)
                TypeUtils.float32Type, (System.Single.MinValue |> double, System.Single.MaxValue |> double)
                TypeUtils.float64Type, (System.Double.MinValue |> double, System.Double.MaxValue |> double) ]
        let getSegment leftTyp rightTyp =
            let min1, max1 = minMaxOf.[leftTyp]
            let min2, max2 = minMaxOf.[rightTyp]
            match min1 < min2, max1 < max2 with
            | true, true   -> min2, max1
            | true, false  -> min2, max2
            | false, true  -> min1, max1
            | false, false -> min1, max2
        let canCastWithoutOverflow term targetTermType =
            let (<<=) = API.Arithmetics.(<<=)
            assert(Terms.TypeOf term |> Types.IsNumeric)
            let termType = Terms.TypeOf term
            if isSubset termType targetTermType then True
            elif termType = TypeUtils.int64Type && targetTermType = TypeUtils.uint64Type then
                let int64Zero = MakeNumber (0 |> int64)
                int64Zero <<= term
            elif termType = TypeUtils.uint64Type && targetTermType = TypeUtils.int64Type then
                let uint64RightBorder = MakeNumber (System.Int64.MaxValue |> uint64)
                term <<= uint64RightBorder
            else
                let min, max = getSegment termType targetTermType
                let leftBorder  = Concrete min termType // must save type info, because min is int64
                let rightBorder = Concrete max termType // must save type info, because max is int64
                (leftBorder <<= term) &&& (term <<= rightBorder)
        let t, cilState = pop cilState
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (canCastWithoutOverflow t targetType, state))
            (fun cilState k ->
                let castedResult = Types.Cast t targetType
                push castedResult cilState |> List.singleton |> k)
            (x.Raise x.OverflowException)
            id

    member private x.ConvOvfUn unsignedSightType targetType (cilState : cilState) =
        let t, cilState = pop cilState
        let unsignedT = castUnchecked unsignedSightType t cilState.state
        x.ConvOvf targetType (push unsignedT cilState)

    member private x.CommonCastClass (cilState : cilState) (term : term) (typ : symbolicType) k =
        let term = castReferenceToPointerIfNeeded term typ cilState.state
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (IsNullReference term ||| Types.IsCast state term typ, state))
            (fun cilState k -> push (Types.Cast term typ) cilState |> List.singleton |> k)
            (x.Raise x.InvalidCastException)
            k
    member private x.CastClass (cfg : cfg) offset (cilState : cilState) : cilState list =
        let term, cilState = pop cilState
        let typ = resolveTermTypeFromMetadata cfg (offset + OpCodes.Castclass.Size)
        x.CommonCastClass cilState term typ pushResultToEvaluationStack

    member private x.PushNewObjResultOnEvaluationStack (cilState : cilState) reference (calledMethod : MethodBase) =
        let valueOnStack =
            if calledMethod.DeclaringType.IsValueType then
                  Memory.ReadSafe cilState.state reference
            else reference
        push valueOnStack cilState

    member x.CommonCall (calledMethodBase : MethodBase) (cilState : cilState) (k : cilState list -> 'a) =
        let call cilState k = x.InlineMethodBaseCallIfNeeded calledMethodBase cilState k
        match calledMethodBase.IsStatic with
        | true -> call cilState k
        | false ->
            let this = Memory.ReadThis cilState.state calledMethodBase
            x.NpeOrInvokeStatementCIL cilState this call k
    member x.RetrieveCalledMethodAndArgs (opCode : OpCode) (calledMethodBase : MethodBase) (cilState : cilState) =
        let args, cilState = retrieveActualParameters calledMethodBase cilState
        let hasThis = not (calledMethodBase.IsStatic || opCode = OpCodes.Newobj)
        let this, cilState = if hasThis then pop cilState |> mapfst Some else None, cilState
        this, args, cilState

    member x.Call (cfg : cfg) offset (cilState : cilState) =
        let calledMethod = resolveMethodFromMetadata cfg (offset + OpCodes.Call.Size)
        methodInterpreter.InitializeStatics cilState calledMethod.DeclaringType (fun cilState ->
        let this, args, cilState = x.RetrieveCalledMethodAndArgs OpCodes.Call calledMethod cilState
        methodInterpreter.ReduceFunctionSignatureCIL cilState calledMethod this (Some args) (fun cilState ->
        x.CommonCall calledMethod cilState id))
    member x.CommonCallVirt (ancestorMethodBase : MethodBase) (cilState : cilState) (k : cilState list -> 'a) =
        let this = Memory.ReadThis cilState.state ancestorMethodBase
        let call (cilState : cilState) k =
            if ancestorMethodBase.IsVirtual && not ancestorMethodBase.IsFinal then
                let methodInfo = ancestorMethodBase :?> MethodInfo
                x.CallVirtualMethod methodInfo cilState k
            else
                x.InlineMethodBaseCallIfNeeded ancestorMethodBase cilState k
        x.NpeOrInvokeStatementCIL cilState this call k
    member x.CallVirt (cfg : cfg) offset (cilState : cilState) =
        let retrieveMethodInfo methodPtr =
            match methodPtr.term with
            | Concrete(:? Tuple<MethodInfo, term> as tuple, _) -> snd tuple, (fst tuple :> MethodBase)
            | _ -> __unreachable__()
        let ancestorMethod = resolveMethodFromMetadata cfg (offset + OpCodes.Call.Size)
        let thisOption, args, cilState = x.RetrieveCalledMethodAndArgs OpCodes.Callvirt ancestorMethod cilState
        let this, methodToCall = // TODO: do better #do
            match thisOption with
            | Some this when ancestorMethod.DeclaringType.IsSubclassOf typedefof<Delegate> && ancestorMethod.Name = "Invoke" && this <> NullRef ->
                let deleg = Memory.ReadDelegate cilState.state this
                let target, mi = retrieveMethodInfo deleg
                if target = NullRef then thisOption, mi else Some target, mi
            | _ -> thisOption, ancestorMethod
        // NOTE: there is no need to initialize statics, because they were initialized before ``newobj'' execution
        // NOTE: It is not quite strict to ReduceFunctionSignature here because, but it does not matter because signatures of virtual methods are the same
        methodInterpreter.InitializeStatics cilState methodToCall.DeclaringType (fun cilState ->
        methodInterpreter.ReduceFunctionSignatureCIL cilState methodToCall this (Some args) (fun cilState ->
        x.CommonCallVirt methodToCall cilState id))
    member x.ReduceArrayCreation (arrayType : System.Type) (cilState : cilState) (parameters : term list) k =
        let arrayTyp = Types.FromDotNetType arrayType
        Memory.AllocateDefaultArray cilState.state parameters arrayTyp |> k
    member x.CommonCreateDelegate (ctor : ConstructorInfo) (cilState : cilState) (args : term list) k =
        let target, methodPtr =
            assert(List.length args = 2)
            args.[0], args.[1]
        let retrieveMethodInfo methodPtr =
            match methodPtr.term with
            | Concrete(:? MethodInfo as mi, _) -> mi
            | _ -> __unreachable__()
        let invoke cilState =
            GuardedApplyCIL cilState methodPtr
                (fun cilState methodPtr k ->
                    BranchOnNullCIL cilState target // TODO: can target be null? #do
                        (x.Raise x.NullReferenceException)
                        (x.InlineMethodBaseCallIfNeeded (retrieveMethodInfo methodPtr))
                        k)
        let typ = Types.FromDotNetType ctor.DeclaringType
        let lambda = Lambdas.make (retrieveMethodInfo methodPtr, target) typ
        Memory.AllocateDelegate cilState.state lambda |> k

    member x.CommonNewObj isCallNeeded (constructorInfo : ConstructorInfo) (cilState : cilState) (args : term list) (k : cilState list -> 'a) : 'a =
        __notImplemented__()
//        let typ = constructorInfo.DeclaringType
//        let constructedTermType = typ |> Types.FromDotNetType cilState.state
//        let blockCase (cilState : cilState) =
//            let callConstructor (cilState : cilState) reference afterCall =
//                if isCallNeeded then
//                    methodInterpreter.ReduceFunctionSignatureCIL cilState constructorInfo (Some reference) (Specified args) false (fun cilState ->
//                    x.InlineMethodBaseCallIfNeeded constructorInfo cilState afterCall)
//                else withResultState reference cilState.state |> changeState cilState |> List.singleton
//            let referenceTypeCase (cilState : cilState) =
//                let ref, state = Memory.AllocateDefaultClass cilState.state constructedTermType
//                callConstructor (withState state cilState) ref (List.map (pushToOpStack ref))
//            let valueTypeCase (cilState : cilState) =
//                let freshValue = Memory.DefaultOf constructedTermType
//                let ref, state = Memory.AllocateTemporaryLocalVariable cilState.state typ freshValue
//                let modifyResult (cilState : cilState) =
//                    let value = Memory.ReadSafe cilState.state ref
//                    pushToOpStack value cilState
//                callConstructor (withState state cilState) ref (List.map modifyResult)
//            if Types.IsValueType constructedTermType then valueTypeCase cilState
//            else referenceTypeCase cilState
//        let nonDelegateCase (cilState : cilState) =
//            if typ.IsArray && constructorInfo.GetMethodBody() = null
//                then x.ReduceArrayCreation typ cilState args id
//                else blockCase cilState
//        if Reflection.IsDelegateConstructor constructorInfo
//            then x.CommonCreateDelegate constructorInfo cilState args k
//            else nonDelegateCase cilState |> k

    member x.NewObj (cfg : cfg) offset (cilState : cilState) =
        let calledMethod = resolveMethodFromMetadata cfg (offset + OpCodes.Newobj.Size)
        assert(calledMethod.IsConstructor)
        let constructorInfo = calledMethod :?> ConstructorInfo
        let typ = constructorInfo.DeclaringType
        methodInterpreter.InitializeStatics cilState constructorInfo.DeclaringType (fun cilState ->
        let this, args, cilState = x.RetrieveCalledMethodAndArgs OpCodes.Newobj calledMethod cilState
        assert(Option.isNone this)
        let constructedTermType = Types.FromDotNetType typ
        let wasConstructorCalled (beforeCall : cilState) (afterCall : cilState) =
            Memory.CallStackSize afterCall.state = Memory.CallStackSize beforeCall.state // TODO: why equality?
        let modifyValueResultIfConstructorWasCalled (beforeCall : cilState) (afterCall : cilState) =
            if wasConstructorCalled beforeCall afterCall then pushNewObjForValueTypes afterCall
            else afterCall

        let blockCase (cilState : cilState) =
            let callConstructor (cilState : cilState) reference afterCall =
                methodInterpreter.ReduceFunctionSignatureCIL cilState constructorInfo (Some reference) (Some args) (fun cilState ->
                x.InlineMethodBaseCallIfNeeded constructorInfo cilState afterCall)

            if Types.IsValueType constructedTermType || typ = typeof<IntPtr> then
                let freshValue = Memory.DefaultOf constructedTermType
                let ref, state = Memory.AllocateTemporaryLocalVariable cilState.state typ freshValue
                let cilState = cilState |> withState state |> push ref // NOTE: ref is used to retrieve constructed struct
                callConstructor cilState ref (List.map (modifyValueResultIfConstructorWasCalled cilState))
            else
                let ref, state = Memory.AllocateDefaultClass cilState.state constructedTermType
                let cilState = cilState |> withState state |> push ref // NOTE: ref is used as result afterCall
                callConstructor cilState ref id

        let k (reference, state) =
            let newIp = moveInstruction (fallThroughTarget cfg.methodBase offset) (currentIp cilState)
            cilState |> withState state |> push reference |> setCurrentIp newIp |> List.singleton

        if Reflection.isDelegateConstructor constructorInfo then
            x.CommonCreateDelegate constructorInfo cilState args k
        elif typ.IsArray && constructorInfo.GetMethodBody() = null then
            x.ReduceArrayCreation typ cilState args k
        else blockCase cilState)

    member x.LdsFld addressNeeded (cfg : cfg) offset (cilState : cilState) =
        let newIp = moveInstruction (fallThroughTarget cfg.methodBase offset) (currentIp cilState)
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Ldsfld.Size)
        assert (fieldInfo.IsStatic)
        methodInterpreter.InitializeStatics cilState fieldInfo.DeclaringType (fun cilState ->
        let declaringTermType = Types.FromDotNetType fieldInfo.DeclaringType
        let fieldId = Reflection.wrapField fieldInfo
        let value = if addressNeeded
                    then StaticField(declaringTermType, fieldId) |> Ref
                    else Memory.ReadStaticField cilState.state declaringTermType fieldId
        push value cilState |> setCurrentIp newIp |> List.singleton)
    member private x.StsFld (cfg : cfg) offset (cilState : cilState) =
        let newIp = moveInstruction (fallThroughTarget cfg.methodBase offset) (currentIp cilState) // TODO: remove this copy-paste
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Stsfld.Size)
        assert(fieldInfo.IsStatic)
        methodInterpreter.InitializeStatics cilState fieldInfo.DeclaringType (fun cilState ->
        let declaringTermType = Types.FromDotNetType fieldInfo.DeclaringType
        let fieldId = Reflection.wrapField fieldInfo
        let value, cilState = pop cilState
        let fieldType = Types.FromDotNetType fieldInfo.FieldType
        let value = castUnchecked fieldType value cilState.state
        let state = Memory.WriteStaticField cilState.state declaringTermType fieldId value
        cilState |> withState state |> setCurrentIp newIp |> List.singleton)
    member x.LdFldWithFieldInfo (fieldInfo : FieldInfo) addressNeeded (cilState : cilState) =
        assert(not fieldInfo.IsStatic)
        let target, cilState = pop cilState
        let loadWhenTargetIsNotNull (cilState : cilState) k =
            let createCilState value = push value cilState |> List.singleton |> k
            let fieldId = Reflection.wrapField fieldInfo
            if fieldInfo.DeclaringType = typeof<IntPtr> then // TODO: make better #do
                if addressNeeded then createCilState target
                else Memory.ReadSafe cilState.state target |> createCilState
            else
                if addressNeeded then Memory.ReferenceField cilState.state target fieldId |> createCilState
                else Memory.ReadField cilState.state target fieldId |> createCilState
        x.NpeOrInvokeStatementCIL cilState target loadWhenTargetIsNotNull id
    member x.LdFld addressNeeded (cfg : cfg) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Ldfld.Size)
        x.LdFldWithFieldInfo fieldInfo addressNeeded cilState
    member x.StFld (cfg : cfg) offset (cilState : cilState) =
        let fieldInfo = resolveFieldFromMetadata cfg (offset + OpCodes.Stfld.Size)
        assert(not fieldInfo.IsStatic)
        let value, targetRef, cilState = pop2 cilState
        let storeWhenTargetIsNotNull (cilState : cilState) k =
            let fieldType = Types.FromDotNetType fieldInfo.FieldType
            let value = castUnchecked fieldType value cilState.state
            let reference =
                if fieldInfo.DeclaringType = typeof<System.IntPtr> then targetRef
                else Reflection.wrapField fieldInfo |> Memory.ReferenceField cilState.state targetRef
            Memory.WriteSafe cilState.state reference value |> List.map (changeState cilState) |> k
        x.NpeOrInvokeStatementCIL cilState targetRef storeWhenTargetIsNotNull id
    member private x.LdElemWithCast cast (cilState : cilState) : cilState list =
        let index, arrayRef, cilState = pop2 cilState
        let uncheckedLdElem (cilState : cilState) k =
            let value = Memory.ReadArrayIndex cilState.state arrayRef [index]
            let castedValue = cast value cilState.state
            push castedValue cilState |> List.singleton |> k
        let checkedLdElem (cilState : cilState) k =
            let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
            x.AccessArray uncheckedLdElem cilState length index k
        x.NpeOrInvokeStatementCIL cilState arrayRef checkedLdElem id
    member private x.LdElemTyp typ (cilState : cilState) = x.LdElemWithCast (castUnchecked typ) cilState
    member private x.LdElem (cfg : cfg) offset (cilState : cilState) =
        let typ = resolveTermTypeFromMetadata cfg (offset + OpCodes.Ldelem.Size)
        x.LdElemTyp typ cilState
    member private x.LdElemRef = x.LdElemWithCast always
    member private x.LdElema (cfg : cfg) offset (cilState : cilState) =
        let typ = resolveTermTypeFromMetadata cfg (offset + OpCodes.Ldelema.Size)
        let index, arrayRef, cilState = pop2 cilState
        let referenceLocation (cilState : cilState) k =
            let value = Memory.ReferenceArrayIndex arrayRef [index]
            push value cilState |> List.singleton |> k
        let checkTypeMismatch (cilState : cilState) (k : cilState list -> 'a) =
            let elementType = MostConcreteTypeOfHeapRef cilState.state arrayRef |> Types.ElementType
            StatedConditionalExecutionAppendResultsCIL cilState
                // TODO: types must be equal or we need to cast? #do
                (fun state k -> k (Types.TypeIsType typ elementType &&& Types.TypeIsType elementType typ, state))
                referenceLocation
                (x.Raise x.ArrayTypeMismatchException)
                k
        let checkIndex (cilState : cilState) k =
            let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
            x.AccessArray checkTypeMismatch cilState length index k
        x.NpeOrInvokeStatementCIL cilState arrayRef checkIndex id
    member private x.StElemWithCast (cilState : cilState) =
        let value, index, arrayRef, cilState = pop3 cilState
        let baseType = MostConcreteTypeOfHeapRef cilState.state arrayRef |> Types.ElementType
        let checkedStElem (cilState : cilState) (k : cilState list -> 'a) =
            let typeOfValue = TypeOf value
            let uncheckedStElem (cilState : cilState) (k : cilState list -> 'a) =
                let casted = castUnchecked baseType value cilState.state
                Memory.WriteArrayIndex cilState.state arrayRef [index] casted |> List.map (changeState cilState) |> k
            let checkTypeMismatchBasedOnTypeOfValue cond (cilState : cilState) =
                StatedConditionalExecutionAppendResultsCIL cilState
                    (fun state k -> k (cond, state))
                    uncheckedStElem
                    (x.Raise x.ArrayTypeMismatchException)
            let checkTypeMismatch (cilState : cilState) (k : cilState list -> 'a) =
                if Types.IsValueType typeOfValue then
                    checkTypeMismatchBasedOnTypeOfValue True cilState k
                else
                    checkTypeMismatchBasedOnTypeOfValue (Types.RefIsAssignableToType cilState.state value baseType) cilState k
            let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
            x.AccessArray checkTypeMismatch cilState length index k
        x.NpeOrInvokeStatementCIL cilState arrayRef checkedStElem id
    member private x.StElemTyp _ (cilState : cilState) =
        x.StElemWithCast cilState
    member private x.StElem (cfg : cfg) offset (cilState : cilState) =
        let typ = resolveTermTypeFromMetadata cfg (offset + OpCodes.Stelem.Size)
        x.StElemTyp typ cilState
    member private x.StElemRef = x.StElemWithCast
    member private x.LdLen (cilState : cilState) =
        let arrayRef, cilState = pop cilState
        let ldlen (cilState : cilState) k =
            let length = Memory.ArrayLengthByDimension cilState.state arrayRef (MakeNumber 0)
            push length cilState |> List.singleton |> k
        x.NpeOrInvokeStatementCIL cilState arrayRef ldlen id
    member private x.LdVirtFtn (_ : cfg) _ (_ : cilState) =
        __notImplemented__()
//        let ancestorMethodBase = resolveMethodFromMetadata cfg (offset + OpCodes.Ldvirtftn.Size)
//        match cilState.opStack with
//        | this :: stack ->
//            let ldvirtftn (cilState : cilState) k =
//                assert(isReference this)
//                let t = this |> SightTypeOfRef |> Types.ToDotNetType
//                let methodInfo = t.GetMethod(ancestorMethodBase.Name, allBindingFlags)
//                let methodPtr = Terms.Concrete methodInfo (Types.FromDotNetType cilState.state (methodInfo.GetType()))
//                k [methodPtr, cilState]
//            x.NpeOrInvokeStatement {cilState with opStack = stack} this ldvirtftn pushFunctionResults
//        | _ -> __corruptedStack__()

    member x.BoxNullable (t : System.Type) (v : term) (cilState : cilState) : cilState list =
        // TODO: move it to Reflection.fs; add more validation in case if .NET implementation does not have these fields
        let boxValue (cilState : cilState) =
            let value, cilState = pop cilState
            let address, state = Memory.BoxValueType cilState.state value
            cilState |> withState state |> push address
        let hasValueCase (cilState : cilState) k =
            let valueFieldInfo = t.GetField("value", Reflection.instanceBindingFlags)
            x.LdFldWithFieldInfo valueFieldInfo false (push v cilState) |> List.map boxValue |> k
        let boxNullable (hasValue, cilState : cilState) k =
            StatedConditionalExecutionAppendResultsCIL cilState
                (fun state k -> k (hasValue, state))
                hasValueCase
                (fun cilState k -> cilState |> push NullRef |> List.singleton |> k)
                k
        let hasValueFieldInfo = t.GetField("hasValue", Reflection.instanceBindingFlags)
        let hasValueResults = x.LdFldWithFieldInfo hasValueFieldInfo false (push v cilState) |> List.map pop
        Cps.List.mapk boxNullable hasValueResults (List.concat >> pushResultToEvaluationStack)

    member x.Box (cfg : cfg) offset (initialCilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Box.Size)
        let termType = Types.FromDotNetType t
        let v, cilState = pop initialCilState
        if Types.IsValueType termType then
            if Types.TypeIsNullable termType then x.BoxNullable t v cilState
            else allocateValueTypeInHeap v cilState
        else initialCilState |> List.singleton
    member private x.UnboxCommon (cilState : cilState) (obj : term) (t : System.Type) (handleRestResults : term * state -> term * state) (k : cilState list -> 'a) =
        let nonExceptionCont (cilState : cilState) res state k =
            cilState |> withState state |> push res |> List.singleton |> k
        let termType = Types.FromDotNetType t
        assert(IsReference obj)
        assert(Types.IsValueType termType)
        let nullCase (cilState : cilState) (k : cilState list -> 'a) : 'a = // TODO: mb too complex #do
            if Types.TypeIsNullable termType then // TODO: here can be type Null #do
                let nullableTerm = Memory.DefaultOf termType
                let address, state = Memory.BoxValueType cilState.state nullableTerm
                let res, state = handleRestResults (HeapReferenceToBoxReference address, state)
                nonExceptionCont cilState res state k
            else
                x.Raise x.NullReferenceException cilState k
        let nullableCase (cilState : cilState) =
            let underlyingTypeOfNullableT = System.Nullable.GetUnderlyingType t
            StatedConditionalExecutionAppendResultsCIL cilState
                (fun state k -> k (Types.RefIsType state obj (Types.FromDotNetType underlyingTypeOfNullableT), state))
                (fun cilState k ->
                    let value = HeapReferenceToBoxReference obj |> Memory.ReadSafe cilState.state
                    let nullableTerm = Memory.DefaultOf termType
                    let valueField, hasValueField = Reflection.fieldsOfNullable t
                    let nullableTerm = Memory.WriteStructField nullableTerm valueField value
                    let nullableTerm = Memory.WriteStructField nullableTerm hasValueField (MakeBool true)
                    let address, state = Memory.BoxValueType cilState.state nullableTerm
                    let res, state = handleRestResults (HeapReferenceToBoxReference address, state)
                    nonExceptionCont cilState res state k)
                (x.Raise x.InvalidCastException)
        let nonNullCase (cilState : cilState) =
            if Types.TypeIsNullable termType then
                nullableCase cilState
            else
                StatedConditionalExecutionAppendResultsCIL cilState
                    (fun state k -> k (Types.IsCast state obj termType, state))
                    (fun cilState k ->
                        let res, state = handleRestResults (Types.Cast obj termType |> HeapReferenceToBoxReference, cilState.state)
                        cilState |> withState state |> push res |> List.singleton |> k)
                    (x.Raise x.InvalidCastException)
        BranchOnNullCIL cilState obj
            nullCase
            nonNullCase
            k

    member private x.Throw (_ : cfg) _ (cilState : cilState) =
        let error, _ = pop cilState
        BranchOnNullCIL cilState error
            (x.Raise x.NullReferenceException)
            (fun cilState k ->
                //TODO: change current ip
                cilState |> withException (Unhandled error) |> clearEvaluationStackLastFrame |> List.singleton |> k)
            id
    member private x.Unbox (cfg : cfg) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Unbox.Size)
        let obj, cilState = pop cilState
        // TODO: Nullable.GetUnderlyingType for generics; use meta-information of generic type parameter
        if t.IsGenericParameter then __insufficientInformation__ "Unboxing generic parameter"
        x.UnboxCommon cilState obj t id pushResultToEvaluationStack
    member private x.UnboxAny (cfg : cfg) offset (cilState : cilState) =
        let t = resolveTypeFromMetadata cfg (offset + OpCodes.Unbox_Any.Size)
        let termType = Types.FromDotNetType t
        let valueType = Types.FromDotNetType typeof<System.ValueType>
        let obj, cilState = pop cilState
        // TODO: Nullable.GetUnderlyingType for generics; use meta-information of generic type parameter
        if t.IsGenericParameter then __insufficientInformation__ "Can't introduce generic type X for equation: T = Nullable<X>"
        StatedConditionalExecutionAppendResultsCIL cilState
            (fun state k -> k (Types.TypeIsType termType valueType, state))
            (fun cilState k ->
                let handleRestResults (address, state : state) = Memory.ReadSafe state address, state
                x.UnboxCommon cilState obj t handleRestResults k)
            (fun state k -> x.CommonCastClass state obj termType k)
            pushResultToEvaluationStack

    member private this.CommonDivRem performAction (cilState : cilState) =
        let integerCase (cilState : cilState) x y minusOne minValue =
            assert(TypeOf x = TypeOf y)
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Arithmetics.IsZero y, state))
                (this.Raise this.InvalidCastException)
                (fun cilState ->
                    StatedConditionalExecutionCIL cilState
                        (fun state k -> k ((x === minValue) &&& (y === minusOne), state))
                        (this.Raise this.InvalidCastException)
                        (fun cilState k -> cilState |> push (performAction x y) |> List.singleton |> k))
                id
        let y, x, cilState = pop2 cilState
        match y, x with
        | TypeUtils.Float, TypeUtils.Float -> cilState |> push (performAction x y) |> List.singleton
        | TypeUtils.Int64, _
        | TypeUtils.UInt64, _
        | _, TypeUtils.Int64
        | _, TypeUtils.UInt64 -> integerCase cilState x y TypeUtils.Int64.MinusOne TypeUtils.Int64.MinValue
        | _ -> integerCase cilState x y TypeUtils.Int32.MinusOne TypeUtils.Int32.MinValue
        | _ -> __unreachable__()
    member private this.Div (cilState : cilState) =
        let div x y = API.PerformBinaryOperation OperationType.Divide x y id
        this.CommonDivRem div cilState

    member private this.Rem (cilState : cilState) =
        let rem x y = API.PerformBinaryOperation OperationType.Remainder x y id
        this.CommonDivRem rem cilState

    member private this.CommonUnsignedDivRem isRem performAction (cilState : cilState) =
        let y, x, cilState = pop2 cilState
        match y, x with
        | _ when TypeUtils.isInteger x && TypeUtils.isInteger y ->
            let x = makeUnsignedInteger x id
            let y = makeUnsignedInteger y id
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (Arithmetics.IsZero y, state))
                (this.Raise this.DivideByZeroException)
                (fun cilState k -> cilState |> push (performAction x y) |> List.singleton |> k)
                id
        | TypeUtils.Float, _
        | _, TypeUtils.Float when isRem -> internalfailf "Rem.Un is unspecified for Floats"
        | _ -> internalfailf "incompatible operands for %s" (if isRem then "Rem.Un" else "Div.Un")
    member private this.DivUn (cilState : cilState) =
        let div x y = API.PerformBinaryOperation OperationType.Divide x y id
        this.CommonUnsignedDivRem false div cilState

    member private this.RemUn cilState =
        let rem x y = API.PerformBinaryOperation OperationType.Remainder x y id
        this.CommonUnsignedDivRem true rem cilState

    member private this.UnsignedCheckOverflow checkOverflowForUnsigned (cilState : cilState) =
        let y, x, cilState = pop2 cilState
        match y, x with
        | TypeUtils.Int64, _
        | _, TypeUtils.Int64
        | TypeUtils.UInt64, _
        | _, TypeUtils.UInt64 ->
            let x = makeUnsignedInteger x id
            let y = makeUnsignedInteger y id
            let max = TypeUtils.UInt64.MaxValue
            let zero = TypeUtils.UInt64.Zero
            checkOverflowForUnsigned zero max x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | _ when TypeUtils.isInteger x && TypeUtils.isInteger y ->
            let x, y = makeUnsignedInteger x id, makeUnsignedInteger y id
            let max = TypeUtils.UInt32.MaxValue
            let zero = TypeUtils.UInt32.Zero
            checkOverflowForUnsigned zero max x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | _ -> internalfailf "incompatible operands for UnsignedCheckOverflow"
    member private this.SignedCheckOverflow checkOverflow (cilState : cilState) =
        let y, x, cilState = pop2 cilState
        match y, x with
        | TypeUtils.Int64, _
        | _, TypeUtils.Int64 ->
            let min = TypeUtils.Int64.MinValue
            let max = TypeUtils.Int64.MaxValue
            let zero = TypeUtils.Int64.Zero
            let minusOne = TypeUtils.Int64.MinusOne
            checkOverflow min max zero minusOne x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
        | TypeUtils.UInt64, _
        | _, TypeUtils.UInt64 -> __unreachable__() // instead of add_ovf should be called add_ovf_un
        | TypeUtils.Float, _
        | _, TypeUtils.Float -> __unreachable__() // only integers
        | _ ->
            let min = TypeUtils.Int32.MinValue
            let max = TypeUtils.Int32.MaxValue
            let zero = TypeUtils.Int32.Zero
            let minusOne = TypeUtils.Int32.MinusOne
            checkOverflow min max zero minusOne x y cilState // TODO: maybe rearrange x and y if y is concrete and x is symbolic
    member private this.Add_ovf (cilState : cilState) =
        // min <= x + y <= max
        let checkOverflow min max zero _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            let xMoreThan0 state k = k (x >>= zero, state)
            let yMoreThan0 state k = k (y >>= zero, state)
            let checkOverflowWhenMoreThan0 (state : state) k = // x >= 0 && y >= 0
                PerformBinaryOperation OperationType.Subtract max y (fun diff ->
                k (diff >>= x, state))
            let checkOverflowWhenLessThan0 (state : state) k =
                PerformBinaryOperation OperationType.Subtract min y (fun diff ->
                k (x >>= diff, state))
            let add (cilState : cilState) k = // no overflow
                PerformBinaryOperation OperationType.Add x y (fun sum -> push sum cilState |> List.singleton |> k)
            StatedConditionalExecutionCIL cilState xMoreThan0
                (fun cilState -> // x >= 0
                    StatedConditionalExecutionCIL cilState yMoreThan0
                        (fun cilState -> // y >= 0
                            StatedConditionalExecutionCIL cilState
                                checkOverflowWhenMoreThan0
                                add
                                (this.Raise this.OverflowException))
                        add)
                (fun cilState -> // x < 0
                    StatedConditionalExecutionCIL cilState yMoreThan0
                        add
                        (fun cilState -> // x < 0 && y < 0
                            StatedConditionalExecutionCIL cilState
                                checkOverflowWhenLessThan0
                                add
                                (this.Raise this.OverflowException)))
                id
        this.SignedCheckOverflow checkOverflow cilState
    member private this.Mul_ovf (cilState : cilState) =
        // min <= x * y <= max
        let checkOverflow min max zero _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            let (>>) = API.Arithmetics.(>>)
            let isZero state k = k ((x === zero) ||| (y === zero), state)
            let xMoreThan0 state k = k (x >> zero, state)
            let yMoreThan0 state k = k (y >> zero, state)
            let checkOverflowWhenXM0YM0 (state : state) k = // x > 0 && y > 0
                PerformBinaryOperation OperationType.Divide max y (fun quotient ->
                k (quotient >>= x, state))
            let checkOverflowWhenXL0YL0 (state : state) k = // x < 0 && y < 0
                PerformBinaryOperation OperationType.Divide max y (fun quotient ->
                k (x >>= quotient, state))
            let checkOverflowWhenXM0YL0 (state : state) k = // x > 0 && y < 0
                PerformBinaryOperation OperationType.Divide min x (fun quotient ->
                k (y >>= quotient, state))
            let checkOverflowWhenXL0YM0 (state : state) k = // x < 0 && y > 0
                PerformBinaryOperation OperationType.Divide min y (fun quotient ->
                k (x >>= quotient, state))
            let mul (cilState : cilState) k = // no overflow
                PerformBinaryOperation OperationType.Multiply x y (fun res -> push res cilState |> List.singleton |> k)
            StatedConditionalExecutionCIL cilState isZero
                (fun cilState k -> cilState |> push zero |> List.singleton |> k)
                (fun cilState ->
                    StatedConditionalExecutionCIL cilState
                        xMoreThan0
                        (fun cilState -> // x > 0
                            StatedConditionalExecutionCIL cilState yMoreThan0
                                (fun cilState -> // y > 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXM0YM0
                                        mul
                                        (this.Raise this.OverflowException))
                                (fun cilState -> // y < 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXM0YL0
                                        mul
                                        (this.Raise this.OverflowException)))
                        (fun cilState -> // x < 0
                            StatedConditionalExecutionCIL cilState
                                yMoreThan0
                                (fun cilState -> // y > 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXL0YM0
                                        mul
                                        (this.Raise this.OverflowException))
                                (fun cilState k -> // y < 0
                                    StatedConditionalExecutionCIL cilState
                                        checkOverflowWhenXL0YL0
                                        mul
                                        (this.Raise this.OverflowException)
                                        k)))
                id
        this.SignedCheckOverflow checkOverflow cilState
    member private this.Add_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned _ max x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            StatedConditionalExecutionCIL cilState
                (fun state k ->
                    PerformBinaryOperation OperationType.Subtract max x (fun diff ->
                    k (diff >>= y, state)))
                (fun cilState k -> PerformBinaryOperation OperationType.Add x y (fun res ->
                    cilState |> push res |> List.singleton |> k))
                (this.Raise this.OverflowException)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Mul_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned zero max x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            let isZero state k = k ((x === zero) ||| (y === zero), state)
            StatedConditionalExecutionCIL cilState isZero
                (fun cilState k -> push zero cilState |> List.singleton |> k)
                (fun cilState k ->
                    StatedConditionalExecutionCIL cilState
                        (fun state k ->
                            PerformBinaryOperation OperationType.Divide max x (fun quotient ->
                            k (quotient >>= y, state)))
                        (fun cilState k ->
                            PerformBinaryOperation OperationType.Multiply x y (fun res ->
                                cilState |> push res |> List.singleton |> k))
                        (this.Raise this.OverflowException)
                        k)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Sub_ovf_un (cilState : cilState) =
        let checkOverflowForUnsigned _ _ x y cilState =
            let (>>=) = API.Arithmetics.(>>=)
            StatedConditionalExecutionCIL cilState
                (fun state k -> k (x >>= y, state))
                (fun (cilState : cilState) k -> // no overflow
                    PerformBinaryOperation OperationType.Subtract x y (fun res ->
                    cilState |> push res |> List.singleton |> k))
                (this.Raise this.OverflowException)
                id
        this.UnsignedCheckOverflow checkOverflowForUnsigned cilState
    member private this.Sub_ovf (cilState : cilState) =
        // there is no way to reduce current operation to [x `Add_Ovf` (-y)]
        // min <= x - y <= max
        let checkOverflowForSigned min max zero minusOne x y cilState =
                let (>>=) = API.Arithmetics.(>>=)
                let xGreaterEqualZero state k = k (x >>= zero, state)
                let sub (cilState : cilState) k = // no overflow
                    PerformBinaryOperation OperationType.Subtract x y (fun res ->
                    cilState |> push res |> List.singleton |> k)
                StatedConditionalExecutionCIL cilState
                    xGreaterEqualZero
                    (fun cilState -> // x >= 0 => max - x >= 0 => no overflow for [-1 * (max - x)]
                        StatedConditionalExecutionCIL cilState
                            (fun state k ->
                                PerformBinaryOperation OperationType.Subtract max x (fun diff ->
                                PerformBinaryOperation OperationType.Multiply diff minusOne (fun minusDiff ->
                                k (y >>= minusDiff, state)))) // y >= -(max - x)
                            sub
                            (this.Raise this.OverflowException))
                    (fun cilState -> // x < 0 => no overflow for [min - x] # x < 0 => [min - x] != min => no overflow for (-1) * [min - x]
                        StatedConditionalExecutionCIL cilState
                           (fun state k ->
                                PerformBinaryOperation OperationType.Subtract min x (fun diff ->
                                PerformBinaryOperation OperationType.Multiply diff minusOne (fun minusDiff ->
                                k (minusDiff >>= y, state)))) // -(min - x) >= y
                            sub
                            (this.Raise this.OverflowException))
                    id
        this.SignedCheckOverflow checkOverflowForSigned cilState
    member private x.Newarr (cfg : cfg) offset (cilState : cilState) =
        let (>>=) = API.Arithmetics.(>>=)
        let elemType = resolveTermTypeFromMetadata cfg (offset + OpCodes.Newarr.Size)
        let numElements, cilState = pop cilState
        StatedConditionalExecutionCIL cilState
            (fun state k -> k (numElements >>= TypeUtils.Int32.Zero, state)) // TODO: exception #do
            (fun cilState k ->
                let ref, state = Memory.AllocateVectorArray cilState.state numElements elemType
                cilState |> withState state |> push ref |> List.singleton |> k)
            (this.Raise this.OverflowException)
            id

    member x.InvalidProgramException cilState = methodInterpreter.InvalidProgramException cilState
    member x.NullReferenceException cilState = methodInterpreter.NullReferenceException cilState
    member x.IndexOutOfRangeException cilState = methodInterpreter.IndexOutOfRangeException cilState
    member x.ArrayTypeMismatchException cilState = methodInterpreter.ArrayTypeMismatchException cilState
    member x.DivideByZeroException cilState = methodInterpreter.DivideByZeroException cilState
    member x.OverflowException cilState = methodInterpreter.OverflowException cilState
    member x.ArithmeticException cilState = methodInterpreter.ArithmeticException cilState
    member x.TypeInitializerException qualifiedTypeName innerException cilState =
        methodInterpreter.TypeInitializerException qualifiedTypeName innerException cilState
    member x.InvalidCastException cilState = methodInterpreter.InvalidCastException cilState

    // -------------------------------- ExplorerBase operations -------------------------------------

    member x.ExecuteAllInstructionsForCFGEdges (cfg : cfg) (cilState : cilState) : (cilState list * cilState list * cilState list) =
        let ip = currentIp cilState
        assert(ip.CanBeExpanded())
        let startingOffset = ip.Offset()
        let endOffset =
            let lastOffset = Seq.last cfg.sortedOffsets
            let rec binarySearch l r =
                if l + 1 = r then l
                else
                    let mid = (l + r) / 2
                    if cfg.sortedOffsets.[mid] <= startingOffset then binarySearch mid r
                    else binarySearch l mid
            let index = binarySearch 0 (Seq.length cfg.sortedOffsets)
            if cfg.sortedOffsets.[index] = lastOffset then cfg.ilBytes.Length
            else cfg.sortedOffsets.[index + 1]

        let isIpOfCurrentBasicBlock (ip : ip) =
            match ip with
            | Instruction(i, m) when m = cfg.methodBase -> startingOffset <= i && i < endOffset
            | _ -> false
        x.ExecuteAllInstructionsWhile isIpOfCurrentBasicBlock cilState

    member x.ExecuteOnlyOneInstruction (cilState : cilState) : (cilState list * cilState list * cilState list) =
        x.ExecuteAllInstructionsWhile (always false) cilState

    // returns finishedStates, incompleteStates, erroredStates
    member x.ExecuteAllInstructionsWhile (condition : ip -> bool) (cilState : cilState) : (cilState list * cilState list * cilState list) =
        let rec executeAllInstructions (finishedStates, incompleteStates, errors) cilState k =
            let ip = currentIp cilState
            try
                let allStates = x.MakeStep {cilState with iie = None}
                let newErrors, goodStates = List.partition isError allStates
                let errors = errors @ newErrors // TODO: check it
                match goodStates with
                | _ when List.forall (currentIp >> condition) goodStates ->
                    Cps.List.foldlk executeAllInstructions (finishedStates, incompleteStates, errors) goodStates k
                | _ -> (goodStates @ finishedStates, incompleteStates, errors) |> k
            with
            | :? InsufficientInformationException as iie ->
                let iieCilState = { cilState with iie = Some iie} |> setCurrentIp ip
                (finishedStates, iieCilState :: incompleteStates, errors) |> k
        executeAllInstructions ([],[],[]) cilState id

    member x.IncrementLevelIfNeeded (cfg : cfg) (offset : offset) (cilState : cilState) : cilState =
        let isRecursiveVertex offset =
            if cfg.dfsOut.ContainsKey offset then
                let t1 = cfg.dfsOut.[offset]
                cfg.reverseGraph.[offset] |> Seq.exists (fun w -> cfg.dfsOut.[w] <= t1)
            else false
        if offset = 0 || isRecursiveVertex offset then
            incrementLevel cilState {offset = offset; method = cfg.methodBase}
        else cilState

    member x.MakeStep (cilState : cilState) =
        let cilState = {cilState with stepsNumber = cilState.stepsNumber + 1u}
        let exit () : cilState =
            match cilState.ipStack with
            | Exit _ :: [] when startsFromMethodBeginning cilState ->
                // the whole method is executed
                withCurrentTime [] cilState |> popFrameOf // TODO: #ask Misha about current time
            | Exit _ :: [] ->
                popFrameOf cilState // some part of method is executed
            | Exit m :: ips' when Reflection.isStaticConstructor m ->
                Logger.info "Done with static cctor %s" (Reflection.getFullMethodName m) // TODO: delete (for info) #do
                cilState |> popFrameOf |> withIpStack ips'
            | Exit callee :: (InstructionEndingIp(offset, caller) as ip) :: _ ->
                Logger.info "Done with method %s" (Reflection.getFullMethodName callee) // TODO: delete (for info) #do
                // TODO: assert(isCallIp ip)
                let newIp = moveInstruction (fallThroughTarget caller offset) ip
                let cilState = cilState |> popFrameOf |> setCurrentIp newIp
                let callSite = parseCallSite caller offset
                if callSite.opCode = OpCodes.Newobj && callSite.calledMethod.DeclaringType.IsValueType then
                    pushNewObjForValueTypes cilState
                else cilState
            | Exit _ :: Exit _ :: _ -> __unreachable__()
            | _ -> __unreachable__()
        let rec makeStep' ip k =
            match ip with
            | Instruction(offset, m) ->
                if offset = 0 then Logger.info "Starting to explore method %O" (Reflection.getFullMethodName m) // TODO: delete (for info) #do
                x.ExecuteInstruction m offset cilState |> k
            | Exit _ -> exit () |> List.singleton |> k
            | Leave(EndFinally, [],  dst, m) ->
                setCurrentIp (instruction m dst) cilState |> clearEvaluationStackLastFrame |> List.singleton |> k
            | Leave(EndFinally, ehc :: ehcs,  dst, m) ->
                let ip' = leave (instruction m ehc.HandlerOffset) ehcs dst m
                setCurrentIp ip' cilState |> clearEvaluationStackLastFrame |> List.singleton |> k
            | Leave(ip, ehcs, dst, m) ->
                let makeLeaveIfNeeded (result : cilState) =
                    if List.length result.ipStack = List.length cilState.ipStack then
                        match result.ipStack with
                        | ip :: ips -> {result with ipStack = leave ip ehcs dst m :: ips}
                        | _ -> __unreachable__()
                    else result
                makeStep' ip (fun states ->
                List.map makeLeaveIfNeeded states |> k)
            | _ -> __notImplemented__()
        makeStep' (currentIp cilState) id

    member private x.ExecuteInstruction m offset (cilState : cilState) =
//        Logger.trace "ExecuteInstruction:\n%s" (dump cilState)
        let cfg = CFG.findCfg m
        let opCode = parseInstruction m offset
//        let newIps = moveIp cilState |> List.map (fun cilState -> cilState.ipStack)
        let newSts = opcode2Function.[hashFunction opCode] cfg offset cilState
        let renewInstructionsInfo cilState =
            if isError cilState then cilState
            else
                x.IncrementLevelIfNeeded cfg offset cilState
        newSts |> List.map renewInstructionsInfo
