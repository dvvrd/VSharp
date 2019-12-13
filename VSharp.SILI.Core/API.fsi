namespace VSharp.Core

open VSharp

[<AutoOpen>]
module API =
    val Enter : locationBinding -> state -> ('a -> 'b) -> ('a -> 'b)

    val Configure : IActivator -> unit
    val ConfigureSolver : ISolver -> unit
    val ConfigureSimplifier : IPropositionalSimplifier -> unit
    val Reset : unit -> unit
    val SaveConfiguration : unit -> unit
    val Restore : unit -> unit

    val HigherOrderApply : ICodeLocation -> state -> (term * state -> 'a) -> 'a
    val BranchStatements : state -> (state -> (term * state -> 'a) -> 'b) -> (state -> (term * state -> 'a) -> 'a) -> (state -> (term * state -> 'a) -> 'a) -> (term * state -> 'a) -> 'b
    val BranchStatementsOnNull : state -> term -> (state -> (term * state -> 'a) -> 'a) -> (state -> (term * state -> 'a) -> 'a) -> (term * state -> 'a) -> 'a
    val BranchExpressions : state -> ((term -> 'a) -> 'b) -> ((term -> 'a) -> 'a) -> ((term -> 'a) -> 'a) -> (term -> 'a) -> 'b
    val StatedConditionalExecution : (state -> (state -> (term * state -> 'a) -> 'b) -> (state -> ('item * state -> 'a) -> 'a) -> (state -> ('item * state -> 'a) -> 'a) -> ((term * 'item) list -> 'item) -> (term list -> state list -> state) -> (term -> term -> 'item -> 'item -> 'item) -> (term -> term -> state -> state -> state) -> (term -> 'item) -> ('item * state -> 'a) -> 'b)

    val GuardedApplyExpression : term -> (term -> term) -> term
    val GuardedStatedApplyStatementK : state -> term -> (state -> term -> (term * state -> 'a) -> 'a) -> (term * state -> 'a) -> 'a
    val GuardedErroredStatedApplyk : (state -> term -> ('item * state -> 'a) -> 'a) -> (term -> 'item) -> state -> term -> ((term * 'item) list -> 'item) -> (term list -> state list -> state) -> ('item * state -> 'a) -> 'a

    val PerformBinaryOperation : OperationType -> bool -> state -> term -> term -> (term * state -> 'a) -> 'a
    val PerformUnaryOperation : OperationType -> bool -> state -> termType -> term -> (term * state -> 'a) -> 'a

    [<AutoOpen>]
    module Terms =
        val Nop : term
        val Error : term -> term
        val Concrete : 'a -> termType -> term
        val Constant : string -> ISymbolicConstantSource -> termType -> term
        val Expression : operation -> term list -> termType -> term
        val Struct : fieldId heap -> termType -> term
        val Class : fieldId heap -> term
        val Union : (term * term) list -> term

        val True : term
        val False : term

        val MakeNullRef : unit -> term
        val MakeDefault : termType -> term -> term
        val MakeNumber : 'a -> term

        val TypeOf : term -> termType
        val GetTypeMethod : state -> term -> term * state
        val TypeOfMethod : state -> termType -> term * state
        val BaseTypeOfRef : term -> termType
        val SightTypeOfRef : term -> termType

        val IsStruct : term -> bool
        val IsReference : term -> bool
        val IsNullReference : term -> term

        val (|True|_|) : term -> unit option
        val (|False|_|) : term -> unit option
        val (|LazyInstantiation|_|) : ISymbolicConstantSource -> (term * 'a generalizedHeap option * bool) option
        val (|RecursionOutcome|_|) : ISymbolicConstantSource -> (ICodeLocation * state * term option * bool) option
        val (|Conjunction|_|) : term -> term list option
        val (|Disjunction|_|) : term -> term list option

        val ConstantsOf : term seq -> term System.Collections.Generic.ISet

        val AddConditionToState : state -> term -> state

    module RuntimeExceptions =
        val InvalidCastException : state -> (term -> 'a) -> 'a * state
        val TypeInitializerException : string -> term -> state -> (term -> 'a) -> 'a * state
        val IndexOutOfRangeException : state -> (term -> 'a) -> 'a * state
        val InvalidProgramException : state -> (term -> 'a) -> 'a * state

    module Types =
        val Numeric : System.Type -> termType

        val FromDotNetType : state -> System.Type -> termType
        val ToDotNetType : termType -> System.Type

        val SizeOf : termType -> int

        val TLength : termType
        val IsBool : termType -> bool
        val IsInteger : termType -> bool
        val IsReal : termType -> bool
        val IsPointer : termType -> bool
        val IsValueType : termType -> term

        val String : termType
        val (|StringType|_|) : termType -> unit option

        val elementType : termType -> termType

        val TypeIsType : termType -> termType -> term
        val TypeIsNullable : termType -> term
        val TypeIsRef : termType -> term -> term
        val RefIsType : term -> termType -> term
        val RefIsRef : term -> term -> term
        val CanCast : term -> termType -> term
        val IsCast : state -> termType -> term -> term
        val Cast : state -> term -> termType -> bool -> (state -> term -> termType -> term * state) -> (term * state -> 'b) -> 'b
        val CastReferenceToPointer : state -> term -> term

    [<AutoOpen>]
    module public Operators =
        val (!!) : term -> term
        val (&&&) : term -> term -> term
        val (|||) : term -> term -> term
        val (===) : term -> term -> term
        val (!==) : term -> term -> term
        val conjunction : term seq -> term
        val disjunction : term seq -> term

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

        val ReferenceField : term -> fieldId -> termType -> term
        val ReferenceLocalVariable : stackKey -> term
        val ReferenceStaticField : termType -> fieldId -> termType -> term
        val ReferenceArrayIndex : state -> term -> term list -> term * state

        val Dereference : state -> term -> term * state
        val DereferenceWithoutValidation : state -> term -> term
        val DereferenceLocalVariable : state -> stackKey -> term * state
        val Mutate : state -> term -> term -> term * state
        val ReadBlockField : term -> fieldId -> termType -> term

        val AllocateOnStack : state -> stackKey -> termType -> term -> state
        val AllocateReferenceTypeInHeap : state -> termType -> term -> term * state
        val AllocateValueTypeInHeap : state -> termType -> term -> term * state
        val AllocateDefaultStatic : state -> termType -> state
        val MakeDefaultBlock : termType -> heapFQL -> term
        val AllocateDefaultBlock : state -> termType -> term * state
        val AllocateDefaultArray : state -> term list -> termType -> term * state
        val AllocateInitializedArray : state -> term list -> int -> termType -> term -> term * state
        val AllocateString : string -> state -> term * state

        val IsTypeNameInitialized : termType -> state -> term
        val Dump : state -> string

        val ArrayLength : term -> term
        val ArrayRank : term -> term
        val ArrayLengthByDimension : state -> term -> term -> term * state
        val ArrayLowerBoundByDimension : state -> term -> term -> term * state

        val StringLength : state -> term -> term * state
        val StringCtorOfCharArray : state -> term -> term -> term * state

    module Marshalling =
        val Unmarshal : state -> obj -> term * state
        val CanBeCalledViaReflection : state -> IFunctionIdentifier -> term option -> term list symbolicValue -> bool
        val CallViaReflection : state -> IFunctionIdentifier -> term option -> term list symbolicValue -> (term * state -> 'a) -> 'a

    module Database =
        val QuerySummary : ICodeLocation -> codeLocationSummary
