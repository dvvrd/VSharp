namespace VSharp.Interpreter.IL

open System
open VSharp.Core.API

#nowarn "69"

open VSharp
open VSharp.Core
open CilStateOperations
open System.Collections.Generic
open System.Reflection
open ipOperations

type pob = {loc : ip; lvl : int; fml : term}
type pobStatus =
    | Unknown
    | Witnessed of cilState
    | Unreachable

type codeLocationSummary = { cilState : cilState } // state.returnRegister is used as result
    with
    member x.State = withEvaluationStack emptyEvaluationStack x.cilState |> stateOf
    member x.Result =
        match EvaluationStack.Length x.cilState.state.evaluationStack with
        | 0 -> Nop
        | 1 -> pop x.cilState |> fst
        | _ -> internalfail "EvaluationStack size was bigger than 1"

type codeLocationSummaries = codeLocationSummary list

[<AbstractClass>]
type public ExplorerBase() =
    static let CurrentlyBeingExploredLocations = HashSet<IFunctionIdentifier>()

    static let DetectUnboundRecursion (funcId : IFunctionIdentifier) (s : state) =
        Memory.CallStackContainsFunction s funcId

    member x.InterpretEntryPoint (id : IFunctionIdentifier) k =
        match id with
        | :? IMethodIdentifier as m ->
            assert(m.IsStatic)
            let state = Memory.InitializeStaticMembers Memory.EmptyState (Types.FromDotNetType m.DeclaringType)
            let initialState = makeInitialState m.Method state
            x.Invoke id initialState (List.map (fun cilState -> { cilState = cilState }) >> List.toSeq >> k)
        | _ -> internalfailf "unexpected entry point: expected regular method, but got %O" id


//    member x.AnswerPobs (funcId : IFunctionIdentifier) (k : (pob * pobStatus) seq -> 'a) =
////        let testSuite
//        let k = API.Reset(); fun x -> API.Restore(); k x
//        x.Invoke funcId
//
//        CurrentlyBeingExploredLocations.Add funcId |> ignore
//        let initialStates = x.FormInitialState funcId
//        let invoke cilState = x.Invoke funcId cilState (List.map (fun cilState -> {cilState = cilState}))
//        let resultsAndStates = initialStates |> List.collect invoke
//        CurrentlyBeingExploredLocations.Remove funcId |> ignore
//        k resultsAndStates

    member x.Explore (funcId : IFunctionIdentifier) (k : codeLocationSummary seq -> 'a) =
        let k = Reset(); fun x -> Restore(); k x
        CurrentlyBeingExploredLocations.Add funcId |> ignore
        let initialStates = x.FormInitialState funcId
        let invoke cilState = x.Invoke funcId cilState (List.map (fun cilState -> {cilState = cilState}))
        let resultsAndStates = initialStates |> List.collect invoke
        CurrentlyBeingExploredLocations.Remove funcId |> ignore
        k resultsAndStates

//    member x.AnswerPobs (funcId : IFunctionIdentifier) (k : codeLocationSummary seq -> 'a) =
//        let k = API.Reset(); fun x -> API.Restore(); k x
//        CurrentlyBeingExploredLocations.Add funcId |> ignore
//        let initialStates = x.FormInitialState funcId
//        let invoke cilState = x.Invoke funcId cilState (List.map (fun cilState -> {cilState = cilState}))
//        let resultsAndStates = initialStates |> List.collect invoke
//        CurrentlyBeingExploredLocations.Remove funcId |> ignore
//        k resultsAndStates

    member private x.ReproduceEffectOrUnroll areWeStuck body (id : IFunctionIdentifier) cilState k =
        // every exploration should be made via searcher
        __unreachable__()
//        if areWeStuck then
//            try
//                x.ReproduceEffect id cilState k
//            with
//            | :? InsufficientInformationException ->
//                body cilState k
//        else
//            // explicitly unrolling
//            body cilState k

    member x.EnterRecursiveRegion (funcId : IFunctionIdentifier) cilState body k =
        let shouldStopUnrolling = x.ShouldStopUnrolling funcId cilState
        x.ReproduceEffectOrUnroll shouldStopUnrolling body funcId cilState k

    member x.ShouldStopUnrolling (funcId : IFunctionIdentifier) cilState =
        match Options.RecursionUnrollingMode () with
        | RecursionUnrollingModeType.SmartUnrolling -> DetectUnboundRecursion funcId cilState.state
        | RecursionUnrollingModeType.NeverUnroll -> true
        | RecursionUnrollingModeType.AlwaysUnroll -> false

    abstract ReduceFunction : MethodBase -> cilState -> (cilState list -> 'a) -> 'a
    default x.ReduceFunction (methodBase : MethodBase) (cilState : cilState) k =
        // TODO: do nothing, we have queue
        cilState |> List.singleton |> k
        // TODO: do concrete invocation if possible!
//        let canUseReflection = API.Marshalling.CanBeCalledViaReflection state funcId this parameters
//        if Options.InvokeConcrete () && canUseReflection then
//            API.Marshalling.CallViaReflection state funcId this parameters k
//        else
//            let methodId = x.MakeMethodIdentifier methodBase
//            let invoke state k = x.Invoke methodId state k
//            x.EnterRecursiveRegion methodId cilState invoke k

    static member ReduceFunctionSignature state (funcId : IFunctionIdentifier) this paramValues k =
        let methodBase = funcId.Method
        let parameters = methodBase.GetParameters()
        let getParameterType (param : ParameterInfo) = Types.FromDotNetType param.ParameterType
        let values, areParametersSpecified =
            match paramValues with
            | Some values -> values, true
            | None -> [], false
        let localVarsDecl (lvi : LocalVariableInfo) =
            let stackKey = LocalVariableKey(lvi, methodBase)
            (stackKey, None, Types.FromDotNetType lvi.LocalType)
        let locals =
            match methodBase.GetMethodBody() with
            | null -> []
            | body -> body.LocalVariables |> Seq.map localVarsDecl |> Seq.toList
        let valueOrFreshConst (param : ParameterInfo option) value =
            match param, value with
            | None, _ -> internalfail "parameters list is longer than expected!"
            | Some param, None ->
                let stackKey = ParameterKey param
                match areParametersSpecified with
                | true when param.HasDefaultValue ->
                    let typ = getParameterType param
                    (stackKey, Some(Concrete param.DefaultValue typ), typ)
                | true -> internalfail "parameters list is shorter than expected!"
                | _ -> (stackKey, None, getParameterType param)
            | Some param, Some value -> (ParameterKey param, Some value, getParameterType param)
        let parameters = List.map2Different valueOrFreshConst parameters values
        let parametersAndThis =
            match this with
            | Some thisValue ->
                let thisKey = ThisKey methodBase
                (thisKey, Some thisValue, TypeOf thisValue) :: parameters // TODO: incorrect type when ``this'' is Ref to stack
            | None -> parameters
        Memory.NewStackFrame state funcId (parametersAndThis @ locals) |> k

    member x.ReduceFunctionSignatureCIL (cilState : cilState) (methodBase : MethodBase) this paramValues k =
        let funcId = x.MakeMethodIdentifier methodBase
        ExplorerBase.ReduceFunctionSignature cilState.state funcId this paramValues (fun state ->
        cilState |> withState state |> pushToIp (instruction methodBase 0) |> k)

    member private x.InitStaticFieldWithDefaultValue state (f : FieldInfo) =
        assert(f.IsStatic)
        let fieldType = Types.FromDotNetType f.FieldType
        let value, state =
            if f.IsLiteral then
                match f.GetValue(null) with // argument means class with field f, so we have null, because f is a static field
                | null -> NullRef, state
                | :? string as str -> Memory.AllocateString str state
                | v when f.FieldType.IsPrimitive || f.FieldType.IsEnum -> Concrete v fieldType, state
                | _ -> __unreachable__()
            else Memory.DefaultOf fieldType, state
        let targetType = Types.FromDotNetType f.DeclaringType
        let fieldId = Reflection.wrapField f
        Memory.WriteStaticField state targetType fieldId value

    // NOTE: When executing ldsfld, call and so on, we should previously initialize statics.
    // NOTE: Continuation 'whenInitializedCont' contains exploration of current instruction 'I' on ipStack.
    // NOTE: If statics was already initialized or we have no static constructor,
    //       then we can continue to explore instructions in continuation 'whenInitializedCont'.
    // NOTE: Otherwise, we need to add static constructor to ipStack (so queue will explore it instruction by instruction)
    //       without calling continuation 'whenInitializedCont'.
    // NOTE: After exploration of static constructor, queue will contain the same instruction 'I',
    //       that caused statics initialization, so queue will try again to explore this instruction,
    //       but at that moment statics will be already initialized
    member x.InitializeStatics (cilState : cilState) (t : Type) whenInitializedCont =
        let fields = t.GetFields(Reflection.staticBindingFlags)
        match t with
        | _ when t.IsGenericParameter -> whenInitializedCont cilState
        | _ ->
            let termType = Types.FromDotNetType t
            let typeInitialized = Memory.IsTypeInitialized cilState.state termType
            match typeInitialized with
            | True -> whenInitializedCont cilState
            | _ ->
                let staticConstructor = t.GetConstructors(Reflection.staticBindingFlags) |> Array.tryHead
                let state = Memory.InitializeStaticMembers cilState.state termType
                let state = Seq.fold x.InitStaticFieldWithDefaultValue state fields
                let cilState = withState state cilState
                match staticConstructor with
                | Some cctor -> x.ReduceFunctionSignatureCIL cilState cctor None (Some []) List.singleton
                | None -> whenInitializedCont cilState
                // TODO: make assumption ``Memory.withPathCondition state (!!typeInitialized)''

    member x.CallAbstractMethod (funcId : IFunctionIdentifier) state k =
        __insufficientInformation__ "Can't call abstract method %O, need more information about the object type" funcId

    static member FormInitialStateWithoutStatics (funcId : IFunctionIdentifier) =
        let this, state(*, isMethodOfStruct*) =
            match funcId with
            | :? IMethodIdentifier as m ->
                let declaringType = Types.FromDotNetType m.DeclaringType
                let initialState = Memory.InitializeStaticMembers Memory.EmptyState declaringType
                (if m.IsStatic then None else Memory.MakeSymbolicThis m.Method |> Some), initialState
            | _ -> __notImplemented__()
        let state = Option.fold (fun state this -> !!(IsNullReference this) |> WithPathCondition state) state this
        ExplorerBase.ReduceFunctionSignature state funcId this None id
    member x.FormInitialState (funcId : IFunctionIdentifier) : cilState list =
        let state = ExplorerBase.FormInitialStateWithoutStatics funcId
        let cilState = makeInitialState funcId.Method state
        x.InitializeStatics cilState funcId.Method.DeclaringType (List.singleton)

    abstract CreateException : System.Type -> term list -> cilState -> cilState list
    default x.CreateException exceptionType arguments cilState =
        assert (not <| exceptionType.IsValueType)
        let cilState = clearEvaluationStackLastFrame cilState
        let constructors = exceptionType.GetConstructors()
        let argumentsLength = List.length arguments
        let argumentsTypes =
            List.map (TypeOf >> Types.ToDotNetType) arguments
        let ctors =
            constructors
            |> List.ofArray
            |> List.filter (fun (ci : ConstructorInfo)
                             -> ci.GetParameters().Length = argumentsLength
                                && ci.GetParameters()
                                   |> Seq.forall2(fun p1 p2 -> p2.ParameterType.IsAssignableFrom(p1)) argumentsTypes)
        assert(List.length ctors = 1)
        let ctor = List.head ctors
        let fullConstructorName = Reflection.getFullMethodName ctor
        assert (Loader.hasRuntimeExceptionsImplementation fullConstructorName)
        let proxyCtor = Loader.getRuntimeExceptionsImplementation fullConstructorName
        x.ReduceFunctionSignatureCIL cilState proxyCtor None (Some arguments) List.singleton

    member x.InvalidProgramException cilState =
        x.CreateException typeof<System.InvalidProgramException> [] cilState
    member x.NullReferenceException cilState =
        x.CreateException typeof<System.NullReferenceException> [] cilState
    member x.IndexOutOfRangeException cilState =
        x.CreateException typeof<System.IndexOutOfRangeException> [] cilState
    member x.ArrayTypeMismatchException cilState =
        x.CreateException typeof<System.ArrayTypeMismatchException> [] cilState
    member x.DivideByZeroException cilState =
        x.CreateException typeof<System.DivideByZeroException> [] cilState
    member x.OverflowException cilState =
        x.CreateException typeof<System.OverflowException> [] cilState
    member x.ArithmeticException cilState =
        x.CreateException typeof<System.ArithmeticException> [] cilState
    member x.TypeInitializerException qualifiedTypeName innerException (cilState : cilState) =
        let typeName, state = Memory.AllocateString qualifiedTypeName cilState.state
        let args = [typeName; innerException]
        x.CreateException typeof<System.TypeInitializationException> args {cilState with state = state}
    member x.InvalidCastException (cilState : cilState) =
        let message, state = Memory.AllocateString "Specified cast is not valid." cilState.state
        x.CreateException typeof<System.InvalidCastException> [message] {cilState with state = state}

    member x.ExploreAndCompose (funcId : IFunctionIdentifier) (cilState : cilState) (k : cilState list -> 'a) =
        let prepareGenericsLessState (methodId : IMethodIdentifier) state =
            let methodBase = methodId.Method
            if not <| Reflection.isGenericOrDeclaredInGenericType methodBase then methodId :> IFunctionIdentifier, state, false
            else
                let fullyGenericMethod, genericArgs, genericDefs = Reflection.generalizeMethodBase methodBase
                let genericArgs = genericArgs |> Seq.map Types.FromDotNetType |> List.ofSeq
                let genericDefs = genericDefs |> Seq.map Id |> List.ofSeq
                if List.isEmpty genericDefs then methodId :> IFunctionIdentifier, state, false
                else
                    let state = Memory.NewTypeVariables state (List.zip genericDefs genericArgs)
                    (x.MakeMethodIdentifier fullyGenericMethod :> IFunctionIdentifier), state, true

        let newFuncId, cilState, isSubstitutionNeeded =
            match funcId with
            | :? IMethodIdentifier as methodId ->
                let newFunId, state, isSubstitutionNeeded = prepareGenericsLessState methodId cilState.state
                newFunId, {cilState with state = state}, isSubstitutionNeeded
            | _ -> funcId, cilState, false

        let k =
            if isSubstitutionNeeded then
                List.map (fun (cilState : cilState) -> {cilState with state = Memory.PopTypeVariables cilState.state}) >> k
            else k

        x.Explore newFuncId (Seq.map (fun summary ->
//            Logger.trace "ExploreAndCompose: Original CodeLoc = %O New CodeLoc = %O\ngot summary state = %s" funcId newFuncId (dump summary.cilState)
//            Logger.trace "ExploreAndCompose: Left state = %s" (dump cilState)
            let summaryCilState = withCurrentTime [] summary.cilState
            let resultStates = compose cilState summaryCilState
//            List.iter (dump >> (Logger.trace "ExploreAndCompose: Result after composition %s")) resultStates
            resultStates) >> List.ofSeq >> List.concat >> k)

    abstract member AnswerPobs : IFunctionIdentifier -> codeLocation list -> (IDictionary<codeLocation, string> -> 'a) -> 'a
    default x.AnswerPobs _ _ _ = __notImplemented__()
    abstract member Invoke : IFunctionIdentifier -> cilState -> (cilState list -> 'a) -> 'a

    abstract member MakeMethodIdentifier : MethodBase -> IMethodIdentifier

    abstract member ReproduceEffect : IFunctionIdentifier -> cilState -> (cilState list -> 'a) -> 'a
    default x.ReproduceEffect funcId state k = x.ExploreAndCompose funcId state k
