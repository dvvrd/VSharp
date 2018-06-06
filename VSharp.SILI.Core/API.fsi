namespace VSharp.Core

open VSharp

[<AutoOpen>]
module API =
    val Enter : locationBinding -> state -> ('a -> 'b) -> ('a -> 'b)

    val Configure : IActivator -> IInterpreter -> unit
    val ConfigureSolver : ISolver -> unit
    val Reset : unit -> unit
    val SaveConfiguration : unit -> unit
    val Restore : unit -> unit

    val InterpretEntryPoint : IFunctionIdentifier -> (functionSummary -> 'a) -> 'a
    val Explore : IFunctionIdentifier -> (functionSummary -> 'a) -> 'a

    val Call : IFunctionIdentifier -> state -> (state -> (statementResult * state -> 'a) -> 'a) -> (statementResult * state -> 'a) -> 'a
    val ComposeStatements : (statementResult * state) -> seq<'a> -> ('a -> bool) -> (state -> 'a -> (statementResult * state -> 'b) -> 'b) -> (statementResult * state -> 'b) -> 'b    val HigherOrderApply : IFunctionIdentifier -> state -> term list -> termType -> (statementResult * state -> 'a) -> 'a
    val BranchStatements : state -> (state -> (term * state -> 'a) -> 'b) -> (state -> (statementResult * state -> 'a) -> 'a) -> (state -> (statementResult * state -> 'a) -> 'a) -> (statementResult * state -> 'a) -> 'b
    val BranchExpressions : state -> (state -> (term * state -> 'a) -> 'b) -> (state -> (term * state -> 'a) -> 'a) -> (state -> (term * state -> 'a) -> 'a) -> (term * state -> 'a) -> 'b
    val BranchStatementsOnNull : state -> term -> (state -> (statementResult * state -> 'a) -> 'a) -> (state -> (statementResult * state -> 'a) -> 'a) -> (statementResult * state -> 'a) -> 'a
    val BranchExpressionsOnNull : state -> term -> (state -> (term * state -> 'a) -> 'a) -> (state -> (term * state -> 'a) -> 'a) -> (term * state -> 'a) -> 'a

    val GuardedApplyExpressionK : term -> (term -> (term -> 'a) -> 'a) -> (term -> 'a) -> 'a
    val GuardedApplyExpression : term -> (term -> term) -> term
    val GuardedApplyStatement : state -> term -> (state -> term -> (statementResult * state -> 'a) -> 'a) -> (statementResult * state -> 'a) -> 'a
    val GuardedApplyStatelessStatement : term -> (term -> statementResult) -> statementResult

    val PerformBinaryOperation : OperationType -> bool -> state -> System.Type -> term -> term -> (term * state -> 'a) -> 'a
    val PerformUnaryOperation : OperationType -> bool -> state -> termType -> term -> (term * state -> 'a) -> 'a

    [<AutoOpen>]
    module Terms =
        val Nop : term
        val Error : term -> term
        val Concrete : 'a -> termType -> term
        val Constant : string -> ISymbolicConstantSource -> termType -> term
        val Expression : operation -> term list -> termType -> term
        val Struct : symbolicHeap -> termType -> term
        val HeapRef : (term * termType) nonEmptyList -> timestamp transparent -> arrayReferenceTarget -> termType -> term
        val StaticRef : string -> (term * termType) list -> termType option -> term
        val Union : (term * term) list -> term

        val True : term
        val False : term

        val MakeNullRef : termType -> term
        val MakeDefault : termType -> term
        val MakeNumber : 'a -> term
        val MakeLambda : 'a symbolicLambda -> termType -> term
        val MakeDefaultArray : term list -> termType -> term
        val MakeInitializedArray : int -> termType -> term -> term

        val TypeOf : term -> termType
        val (|Lambda|_|) : termNode -> 'a symbolicLambda option
        val (|LazyInstantiation|_|) : ISymbolicConstantSource -> (term * generalizedHeap option * bool) option
        val (|RecursionOutcome|_|) : ISymbolicConstantSource -> (IFunctionIdentifier * state * term option * bool) option
        val (|StaticsInitializedSource|_|) : ISymbolicConstantSource -> (generalizedHeap * term) option
        val (|SymbolicSubtypeSource|_|) : ISymbolicConstantSource -> (termType * termType) option
        val (|Conjunction|_|) : term -> term list option
        val (|Disjunction|_|) : term -> term list option

        val PersistentLocalAndConstraintTypes : (term -> termType -> termType * termType * termType)
        val ConstantsOf : term seq -> term System.Collections.Generic.ISet

    module RuntimeExceptions =
        val NullReferenceException : state -> (term -> 'a) -> 'a * state
        val InvalidCastException : state -> (term -> 'a) -> 'a * state
        val TypeInitializerException : string -> term -> state -> (term -> 'a) -> 'a * state
        val IndexOutOfRangeException : state -> (term -> 'a) -> 'a * state

    module Types =
        val FromDotNetType : state -> System.Type -> termType
        val ToDotNetType : termType -> System.Type
        val WrapReferenceType : termType -> termType
        val NewTypeVariable : System.Type -> termType

        val SizeOf : termType -> int

        val TLength : termType
        val IsBool : termType -> bool
        val IsInteger : termType -> bool
        val IsReal : termType -> bool
        val IsNativeInt : System.Type -> bool

        val String : termType
        val (|StringType|_|) : termType -> unit option

        val IsSubtype : termType -> termType -> term
        val CanCast : state -> termType -> term -> term * state
        val Cast : state -> term -> termType -> bool -> (state -> term -> termType -> statementResult * state) -> (term * state -> 'b) -> 'b
        val HierarchyCast : state -> term -> termType -> (state -> term -> termType -> statementResult * state) -> (term * state -> 'b) -> 'b
        val CastConcrete : 'a -> System.Type -> term
        val CastReferenceToPointer : state -> term -> (term * state -> 'a) -> 'a

    [<AutoOpen>]
    module public ControlFlowConstructors =
        val NoComputation : statementResult
        val NoResult : unit -> statementResult
        val Break : unit -> statementResult
        val Continue : unit -> statementResult
        val Return : term -> statementResult
        val Throw : term -> statementResult
        val Guarded : (term * statementResult) list -> statementResult

    module public ControlFlow =
        val ResultToTerm : statementResult -> term
        val ThrowOrReturn : term -> statementResult
        val ThrowOrIgnore : term -> statementResult
        val ConsumeErrorOrReturn : (term -> statementResult) -> term -> statementResult
        val ComposeSequentially : statementResult -> statementResult -> state -> state -> statementResult * state
        val ConsumeBreak : statementResult -> statementResult
        val PickOutExceptions : statementResult -> (term * term) option * (term * statementResult) list

    [<AutoOpen>]
    module public Operators =
        val (!!) : term -> term
        val (&&&) : term -> term -> term
        val (|||) : term -> term -> term
        val (===) : term -> term -> term
        val (!==) : term -> term -> term

    module public Arithmetics =
        val (===) : term -> term -> term
        val (!==) : term -> term -> term
        val (<<) : term -> term -> term
        val (<<=) : term -> term -> term
        val (>>) : term -> term -> term
        val (>>=) : term -> term -> term
        // Lightweight version: divide by zero exceptions are ignored!
        val (%%%) : term -> term -> term

    module public Memory =
        val EmptyState : state

        val PopStack : state -> state
        val PopTypeVariables : state -> state
        val NewStackFrame : state -> IFunctionIdentifier -> (stackKey * term symbolicValue * termType) list -> state
        val NewScope : state -> (stackKey * term symbolicValue * termType) list -> state
        val NewTypeVariables : state -> (typeId * termType) list -> state

        val ReferenceField : state -> bool -> string -> termType -> term -> term * state
        val ReferenceLocalVariable : state -> stackKey -> bool -> term
        val ReferenceStaticField : state -> bool -> string -> termType -> string -> term * state
        val ReferenceArrayIndex : state -> term -> term list -> term * state

        val Dereference : state -> term -> term * state
        val DereferenceLocalVariable : state -> stackKey -> term * state
        val Mutate : state -> term -> term -> term * state

        val AllocateOnStack : state -> stackKey -> term -> state
        val AllocateInHeap : state -> term -> term * state
        val AllocateDefaultStatic : state -> termType -> string -> state
        val MakeDefaultStruct : termType -> term
        val AllocateString : string -> state -> term * state

        val IsTypeNameInitialized : string -> state -> term
        val Dump : state -> string

        val ArrayLength : term -> term
        val ArrayLengthByDimension : state -> term -> term -> term * state
        val ArrayLowerBoundByDimension : state -> term -> term -> term * state

    module Database =
        val QuerySummary : IFunctionIdentifier -> functionSummary
