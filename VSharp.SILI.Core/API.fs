namespace VSharp.Core

open VSharp

module API =
    let private m = let r = new persistent<_>(always Metadata.empty, id) in r.Reset(); r
    let Enter (location : locationBinding) state k =
        m.Save()
        m.Mutate(State.mkMetadata location state)
        fun x -> m.Restore(); k x

    let Configure activator interpreter =
        State.configure activator
        Explorer.configure interpreter
    let ConfigureSolver solver =
        Common.configureSolver solver
    let Reset() =
        Memory.reset()
        IdGenerator.reset()
    let SaveConfiguration() =
        Memory.saveConfiguration()
        IdGenerator.saveConfiguration()
    let Restore() =
        Memory.restore()
        IdGenerator.restore()

    let InterpretEntryPoint id k = Explorer.interpretEntryPoint id k
    let Explore id k = Explorer.explore id k

    let Call funcId state body k = Explorer.call m.Value funcId state body k
    let ComposeStatements rs statements isContinueConsumer reduceStatement k =
        ControlFlow.composeStatements statements isContinueConsumer reduceStatement (fun state -> Memory.newScope m.Value state []) rs k
    let HigherOrderApply funcId state parameters returnType k = Explorer.higherOrderApply m.Value funcId state parameters returnType k
    let BranchStatements state condition thenBranch elseBranch k =
         Common.statedConditionalExecution state condition thenBranch elseBranch ControlFlow.mergeResults ControlFlow.merge2Results ControlFlow.throwOrIgnore k
    let BranchExpressions state condition thenExpression elseExpression k = Common.statedConditionalExecution state condition thenExpression elseExpression Merging.merge Merging.merge2Terms id k
    let BranchStatementsOnNull state reference thenBranch elseBranch k =
        BranchStatements state (fun state k -> k (Pointers.isNull m.Value reference, state)) thenBranch elseBranch k
    let BranchExpressionsOnNull state reference thenExpression elseExpression k =
        BranchExpressions state (fun state k -> k (Pointers.isNull m.Value reference, state)) thenExpression elseExpression k

    let GuardedApplyExpressionK term mapper k =
        match term.term with
        | Error _ -> k term
        | Union gvs -> Merging.guardedMapk mapper gvs k
        | _ -> mapper term k
    let GuardedApplyExpression term mapper =
        match term.term with
        | Error _ -> term
        | Union gvs -> Merging.guardedMap mapper gvs
        | _ -> mapper term
    let GuardedApplyStatement state term mapper k =
        match term.term with
        | Error e -> k (Throw term.metadata e, state)
        | Union gvs -> Merging.commonGuardedStateMapk mapper gvs state ControlFlow.mergeResults k
        | _ -> mapper state term k
    let GuardedApplyStatelessStatement term mapper =
        match term.term with
        | Error e -> Throw term.metadata e
        | Union gvs -> Merging.commonGuardedMapk (Cps.ret mapper) gvs ControlFlow.mergeResults id
        | _ -> mapper term

    let PerformBinaryOperation op isChecked state t left right k = Operators.simplifyBinaryOperation m.Value op isChecked state t left right k
    let PerformUnaryOperation op isChecked state t arg k = Operators.simplifyUnaryOperation m.Value op isChecked state t arg k

    [<AutoOpen>]
    module public Terms =
        let Nop = Nop
        let Error term = Error m.Value term
        let Concrete obj typ = Concrete m.Value obj typ
        let Constant name source typ = Constant m.Value name source typ
        let Expression op args typ = Expression m.Value op args typ
        let Struct fields typ = Struct m.Value fields typ
        let HeapRef path time arrayTarget typ = HeapView m.Value path time arrayTarget typ
        let StaticRef key path typ = StaticView m.Value key path typ
        let Union gvs = Union m.Value gvs

        let True = True
        let False = False

        let MakeNullRef typ = makeNullRef typ m.Value
        let MakeDefault typ = Memory.mkDefault m.Value typ
        let MakeNumber n = makeNumber n m.Value
        let MakeLambda body signature = Lambdas.make m.Value body signature
        let MakeDefaultArray dimensions typ = Arrays.makeDefault m.Value dimensions typ
        let MakeInitializedArray rank typ initializer = Arrays.fromInitializer m.Value (Memory.tick()) rank typ initializer

        let TypeOf term = typeOf term
        let (|Lambda|_|) t = Lambdas.(|Lambda|_|) t
        let (|LazyInstantiation|_|) s = Memory.(|LazyInstantiation|_|) s
        let (|RecursionOutcome|_|) s = Explorer.(|RecursionOutcome|_|) s
        let (|StaticsInitializedSource|_|) s = Memory.(|StaticsInitializedSource|_|) s
        let (|SymbolicSubtypeSource|_|) s = Common.(|SymbolicSubtypeSource|_|) s
        let (|Conjunction|_|) term = Terms.(|Conjunction|_|) term.term
        let (|Disjunction|_|) term = Terms.(|Disjunction|_|) term.term

        let PersistentLocalAndConstraintTypes = Terms.persistentLocalAndConstraintTypes
        let ConstantsOf terms = discoverConstants terms

    module Types =
        let FromDotNetType (state : state) t = t |> Types.Constructor.fromDotNetType |> State.substituteTypeVariables state
        let ToDotNetType t = Types.toDotNetType t
        let WrapReferenceType t = Types.wrapReferenceType t
        let NewTypeVariable t = Types.Variable.fromDotNetType t

        let SizeOf t = Types.sizeOf t

        let TLength = Arrays.lengthTermType
        let IsBool t = Types.isBool t
        let IsInteger t = Types.isInteger t
        let IsReal t = Types.isReal t
        let IsNativeInt t = Pointers.isNativeInt t

        let String = Types.String
        let (|StringType|_|) t = Types.(|StringType|_|) t

        let IsSubtype leftType rightType = Common.is m.Value leftType rightType
        let CanCast state targetType term = TypeCasting.canCast m.Value state targetType term
        let Cast state term targetType isChecked fail k = TypeCasting.cast m.Value state term targetType isChecked (TypeCasting.primitiveCast m.Value isChecked) fail k
        let HierarchyCast state term targetType fail k = TypeCasting.cast m.Value state term targetType false id fail k
        let CastConcrete value typ = CastConcrete value typ m.Value
        let CastReferenceToPointer state reference k = TypeCasting.castReferenceToPointer m.Value state reference k

    module public ControlFlowConstructors =
        let NoComputation = NoResult Metadata.empty
        let NoResult () = NoResult m.Value
        let Break () = Break m.Value
        let Continue () = Continue m.Value
        let Return (term : term) = Return term.metadata term
        let Throw (term : term) = Throw term.metadata term
        let Guarded grs = Guarded m.Value grs

    module public ControlFlow =
        let ResultToTerm r = ControlFlow.resultToTerm r
        let ThrowOrReturn t = ControlFlow.throwOrReturn t
        let ThrowOrIgnore t = ControlFlow.throwOrIgnore t
        let ConsumeErrorOrReturn consumer t = ControlFlow.consumeErrorOrReturn consumer t
        let ComposeSequentially oldRes newRes oldState newState = ControlFlow.composeSequentially oldRes newRes oldState newState
        let ConsumeBreak r = ControlFlow.consumeBreak r
        let PickOutExceptions r = ControlFlow.pickOutExceptions r

    module public Operators =
        let (!!) x = Propositional.simplifyNegation m.Value x id
        let (&&&) x y = Propositional.simplifyAnd m.Value x y id
        let (|||) x y = Propositional.simplifyOr m.Value x y id
        let (===) x y = Operators.ksimplifyEquality m.Value x y id
        let (!==) x y = Operators.ksimplifyEquality m.Value x y (!!)

    module public Arithmetics =
        let (===) x y = Arithmetics.simplifyEqual m.Value x y id
        let (!==) x y = Arithmetics.simplifyNotEqual m.Value x y id
        let (<<) x y = Arithmetics.simplifyLess m.Value x y id
        let (<<=) x y = Arithmetics.simplifyLessOrEqual m.Value x y id
        let (>>) x y = Arithmetics.simplifyGreater m.Value x y id
        let (>>=) x y = Arithmetics.simplifyGreaterOrEqual m.Value x y id
        let (%%%) x y = Arithmetics.simplifyRemainder m.Value false State.empty (x |> TypeOf |> Types.ToDotNetType) x y fst

    module public Memory =
        let EmptyState = State.empty

        let PopStack state = State.popStack state
        let PopTypeVariables state = State.popTypeVariablesSubstitution state
        let NewStackFrame state funcId parametersAndThis = Memory.newStackFrame state m.Value funcId parametersAndThis
        let NewScope state frame = Memory.newScope m.Value state frame
        let NewTypeVariables state subst = State.pushTypeVariablesSubstitution state subst

        let ReferenceField state followHeapRefs name typ parentRef = Memory.referenceField m.Value state followHeapRefs name typ parentRef
        let ReferenceLocalVariable state location followHeapRefs = Memory.referenceLocalVariable m.Value state location followHeapRefs
        let ReferenceStaticField state followHeapRefs fieldName fieldType typeName = Memory.referenceStaticField m.Value state followHeapRefs fieldName fieldType typeName
        let ReferenceArrayIndex state arrayRef indices = Memory.referenceArrayIndex m.Value state arrayRef indices

        let Dereference state reference = Memory.deref m.Value state reference
        let DereferenceLocalVariable state id = Memory.referenceLocalVariable m.Value state id false |> Memory.deref m.Value state
        let Mutate state reference value = Memory.mutate m.Value state reference value

        let AllocateOnStack state key term = Memory.allocateOnStack m.Value state key term
        let AllocateInHeap state term = Memory.allocateInHeap m.Value state term
        let AllocateDefaultStatic state termType qualifiedTypeName = Memory.mkDefaultStruct m.Value true termType |> Memory.allocateInStaticMemory m.Value state qualifiedTypeName
        let MakeDefaultStruct termType = Memory.mkDefaultStruct m.Value false termType
        let AllocateString str state = Strings.makeString m.Value (Memory.tick()) str |> Memory.allocateInHeap m.Value state

        let IsTypeNameInitialized qualifiedTypeName state = Memory.typeNameInitialized m.Value qualifiedTypeName state
        let Dump state = State.dumpMemory state

        let ArrayLength arrayTerm = Arrays.length arrayTerm
        let ArrayLengthByDimension state arrayRef index = Memory.referenceArrayLength arrayRef index |> Memory.deref m.Value state
        let ArrayLowerBoundByDimension state arrayRef index = Memory.referenceArrayLowerBound arrayRef index |> Memory.deref m.Value state

    module Database =
        let QuerySummary funcId =
            Database.querySummary funcId ||?? lazy(internalfailf "database does not contain exploration results for %O" funcId)

    module RuntimeExceptions =
        let NullReferenceException state thrower =
            let term, state = Memory.npe m.Value state
            thrower term, state
        let InvalidCastException state thrower =
            let message, state = Memory.AllocateString "Specified cast is not valid." state
            let term, state = State.createInstance m.Value typeof<System.InvalidCastException> [message] state
            thrower term, state
        let TypeInitializerException qualifiedTypeName innerException state thrower =
            let args = [makeConcreteString qualifiedTypeName m.Value; innerException]
            let term, state = State.createInstance m.Value typeof<System.TypeInitializationException> args state
            thrower term, state
        let IndexOutOfRangeException state thrower =
            let term, state = State.createInstance m.Value typeof<System.IndexOutOfRangeException> [] state
            thrower term, state
