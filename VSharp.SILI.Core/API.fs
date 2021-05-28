namespace VSharp.Core

open FSharpx.Collections
open VSharp

module API =
    let ConfigureSolver solver =
        SolverInteraction.configureSolver solver
    let ConfigureSimplifier simplifier =
        Propositional.configureSimplifier simplifier

    let Reset() =
        IdGenerator.reset()
    let SaveConfiguration() =
        IdGenerator.saveConfiguration()
    let Restore() =
        IdGenerator.restore()

    let BranchStatements state condition thenStatement elseStatement k =
        Memory.statedConditionalExecutionWithMergek state condition thenStatement elseStatement k
    let BranchStatementsOnNull state reference thenStatement elseStatement k =
        BranchStatements state (fun state k -> k (Pointers.isNull reference, state)) thenStatement elseStatement k
    let BranchExpressions condition thenBranch elseExpression k =
        Common.statelessConditionalExecutionWithMergek condition thenBranch elseExpression k
    let StatedConditionalExecutionAppendResults (state : state) conditionInvocation (thenBranch : (state -> (state list -> 'a) -> 'a)) elseBranch k =
        Memory.commonStatedConditionalExecutionk state conditionInvocation thenBranch elseBranch (fun x y -> [x;y]) (List.concat >> k)
    let StatedConditionalExecution = Memory.commonStatedConditionalExecutionk

    let GuardedApplyExpressionWithPC pc term f = Merging.guardedApplyWithPC pc f term
    let GuardedApplyExpression term f = Merging.guardedApply f term
    let GuardedStatedApplyStatementK state term f k = Memory.guardedStatedApplyk f state term k
    let GuardedStatedApplyk f state term mergeStates k =
        Memory.commonGuardedStatedApplyk f state term mergeStates k

    let PerformBinaryOperation op left right k = Operators.simplifyBinaryOperation op left right k
    let PerformUnaryOperation op arg k = Operators.simplifyUnaryOperation op arg k

    let IsValid state = SolverInteraction.isValid state

    [<AutoOpen>]
    module public Terms =
        let Nop = Nop
        let Concrete obj typ = Concrete obj typ
        let Constant name source typ = Constant name source typ
        let Expression op args typ = Expression op args typ
        let Struct fields typ = Struct fields typ
        let Ref address = Ref address
        let Ptr baseAddress typ offset = Ptr baseAddress typ offset
        let HeapRef address baseType = HeapRef address baseType
        let Union gvs = Union gvs

        let True = True
        let False = False
        let NullRef = nullRef

        let MakeBool b = makeBool b
        let MakeNumber n = makeNumber n
        let MakeIntPtr value state =
            match value.term with
            // Case for references
            | Ref _ -> TypeCasting.castReferenceToPointer state value
            // Case for numerics, that need to be converted to IntPtr (native int)
            | Concrete(_, Numeric _) ->
                // We will never create IntPtr from another numeric, because it's pointless
//                assert(v :?> int = 0) // localloc takes size in native int
                Ptr None Void (Some value)
            // Case for native int
            | Ptr(_, Void, _) -> value
            | _ -> __unreachable__()

        let TypeOf term = typeOf term
        let rec MostConcreteTypeOfHeapRef state ref =
            let getType ref =
                match ref.term with
                | HeapRef(address, sightType) -> Memory.mostConcreteTypeOfHeapRef state address sightType
                | _ -> internalfailf "reading type token: expected heap reference, but got %O" ref
            commonTypeOf getType ref

        let IsStruct term = isStruct term
        let IsReference term = isReference term
        let IsNullReference term = Pointers.isNull term

        let (|ConcreteHeapAddress|_|) t = (|ConcreteHeapAddress|_|) t

        let (|True|_|) t = (|True|_|) t
        let (|False|_|) t = (|False|_|) t
        let (|Conjunction|_|) term = Terms.(|Conjunction|_|) term.term
        let (|Disjunction|_|) term = Terms.(|Disjunction|_|) term.term

        let (|HeapReading|_|) src = Memory.(|HeapReading|_|) src
        let (|ArrayIndexReading|_|) src = Memory.(|ArrayIndexReading|_|) src
        let (|VectorIndexReading|_|) src = Memory.(|VectorIndexReading|_|) src
        let (|StackBufferReading|_|) src = Memory.(|StackBufferReading|_|) src
        let (|StaticsReading|_|) src = Memory.(|StaticsReading|_|) src
        let (|StructFieldSource|_|) src = Memory.(|StructFieldSource|_|) src
        let (|HeapAddressSource|_|) src = Memory.(|HeapAddressSource|_|) src
        let (|TypeInitializedSource|_|) src = Memory.(|TypeInitializedSource|_|) src

        let GetHeapReadingRegionSort src = Memory.getHeapReadingRegionSort src

        let ConstantsOf terms = discoverConstants terms

        let rec HeapReferenceToBoxReference reference =
            match reference.term with
            | HeapRef({term = ConcreteHeapAddress addr}, typ) -> Ref (BoxedLocation(addr, typ))
            | HeapRef _ -> __insufficientInformation__ "Unable to unbox symbolic ref %O" reference
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, HeapReferenceToBoxReference v)) |> Merging.merge
            | _ -> internalfailf "Unboxing: expected heap reference, but got %O" reference

        let WithPathCondition conditionState condition = Memory.withPathCondition conditionState condition
        let IsFalsePathCondition conditionState = PC.isFalse conditionState.pc
        let PathConditionToSeq (pc : pathCondition) = PC.toSeq pc

    module Types =
        let Numeric t = Types.Numeric t
        let ObjectType = Types.objectType
        let IndexType = Types.indexType

        let FromDotNetType t = Types.Constructor.fromDotNetType t
        let ToDotNetType t = Types.toDotNetType t

        let SizeOf t = Types.sizeOf t
        let RankOf t = Types.rankOf t

        let TLength = Types.lengthType
        let IsBool t = Types.isBool t
        let IsInteger t = Types.isInteger t
        let IsReal t = Types.isReal t
        let IsNumeric t = Types.isNumeric t
        let IsPointer t = Types.isPointer t
        let IsValueType t = Types.isValueType t
        let IsArrayType t = Types.isArray t
        let String = Types.String
        let (|StringType|_|) t = Types.(|StringType|_|) t

        let ElementType arrayType = Types.elementType arrayType

        let TypeIsType leftType rightType = TypeCasting.typeIsType leftType rightType
        let TypeIsNullable typ = TypeCasting.isNullable typ
        let TypeIsRef state typ ref = TypeCasting.typeIsRef state typ ref
        let RefIsType state ref typ = TypeCasting.refIsType state ref typ
        let RefIsAssignableToType state ref typ = TypeCasting.refIsAssignableToType state ref typ

        let IsCast state term targetType = TypeCasting.canCast state term targetType
        let CanCastImplicitly term targetType =
            let actualType = TypeOf term
            Types.canCastImplicitly actualType targetType
        let Cast term targetType = TypeCasting.cast term targetType
        let CastReferenceToPointer state reference = TypeCasting.castReferenceToPointer state reference

    module public Operators =
        let (!!) x = simplifyNegation x id
        let (&&&) x y = simplifyAnd x y id
        let (|||) x y = simplifyOr x y id
        let (===) x y = ksimplifyEquality x y id
        let (!==) x y = ksimplifyEquality x y (!!)
        let conjunction xs = conjunction xs
        let disjunction xs = disjunction xs

    module public Arithmetics =
        let (===) x y = simplifyEqual x y id
        let (!==) x y = simplifyNotEqual x y id
        let (<<) x y = simplifyLess x y id
        let (<<=) x y = simplifyLessOrEqual x y id
        let (>>) x y = simplifyGreater x y id
        let (>>=) x y = simplifyGreaterOrEqual x y id
        let (%%%) x y = simplifyRemainder (x |> TypeOf |> Types.ToDotNetType) x y id

        let Mul x y = mul x y
        let Sub x y = sub x y
        let IsZero term = checkEqualZero term id

    module public EvaluationStack =
        let Pop evaluationStack = EvaluationStack.pop evaluationStack
        let PopArguments n evaluationStack = EvaluationStack.popMany n evaluationStack
        let Push x evaluationStack =
            let x' = TypeCasting.castToEvaluationStackType x
            EvaluationStack.push x' evaluationStack
        let GetItem index evaluationStack = EvaluationStack.item index evaluationStack
        let FilterActiveFrame f evaluationStack = EvaluationStack.filterActiveFrame f evaluationStack
        let Union oldStack newStack = EvaluationStack.union oldStack newStack
        let MakeSymbolicActiveFrame f evaluationStack = EvaluationStack.makeSymbolicActiveFrame f evaluationStack
        let Length evaluationStack = EvaluationStack.length evaluationStack
        let ToList evaluationStack = EvaluationStack.toList evaluationStack
        let ClearActiveFrame evaluationStack = EvaluationStack.clearActiveFrame evaluationStack

    module public Memory =
        let EmptyState = Memory.empty
        let PopFrame state = Memory.popFrame state
        let PopTypeVariables state = Memory.popTypeVariablesSubstitution state
        let NewStackFrame state funcId parametersAndThis = Memory.newStackFrame state funcId parametersAndThis
        let NewTypeVariables state subst = Memory.pushTypeVariablesSubstitution state subst

        let rec ReferenceArrayIndex arrayRef indices =
            match arrayRef.term with
            | HeapRef(addr, typ) -> ArrayIndex(addr, indices, symbolicTypeToArrayType typ) |> Ref
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ReferenceArrayIndex v indices)) |> Merging.merge
            | _ -> internalfailf "Referencing array index: expected reference, but got %O" arrayRef
        let rec ReferenceField state reference fieldId =
            match reference.term with
            | HeapRef(address, typ) when fieldId.declaringType.IsValueType ->
                assert(Memory.mostConcreteTypeOfHeapRef state address typ |> Types.ToDotNetType |> fieldId.declaringType.IsAssignableFrom)
                ReferenceField state (HeapReferenceToBoxReference reference) fieldId
            | HeapRef(address, typ) ->
                assert(Memory.mostConcreteTypeOfHeapRef state address typ |> Types.ToDotNetType |> fieldId.declaringType.IsAssignableFrom)
                ClassField(address, fieldId) |> Ref
            | Ref address ->
                assert(Memory.baseTypeOfAddress state address |> Types.isStruct)
                StructField(address, fieldId) |> Ref
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ReferenceField state v fieldId)) |> Merging.merge
            | _ -> internalfailf "Referencing field: expected reference, but got %O" reference

        let ReadSafe state reference =
            let reference =
                // TODO: check of reference is BoxedLocation
                match reference.term with
                | HeapRef _ -> HeapReferenceToBoxReference reference
                | _ -> reference
            Memory.readSafe state reference
        let ReadLocalVariable state location = Memory.readStackLocation state location
        let ReadThis state methodBase = Memory.readStackLocation state (ThisKey methodBase)
        let ReadArgument state parameterInfo = Memory.readStackLocation state (ParameterKey parameterInfo)
        let ReadField state term field =
            let doRead target =
                match target.term with
                | HeapRef _
                | Ref _ -> ReferenceField state target field |> Memory.readSafe state
                | Struct _ -> Memory.readStruct target field
                | _ -> internalfailf "Reading field of %O" term
            Merging.guardedApply doRead term

        let rec ReadArrayIndex state reference indices =
            match reference.term with
            | HeapRef(addr, typ) ->
                let (_, dim, _) as arrayType = Memory.mostConcreteTypeOfHeapRef state addr typ |> symbolicTypeToArrayType
                assert(dim = List.length indices)
                Memory.readArrayIndex state addr indices arrayType
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ReadArrayIndex state v indices)) |> Merging.merge
            | _ -> internalfailf "Reading array index: expected reference, but got %O" reference
        let rec ReadStringChar state reference index =
            match reference.term with
            | HeapRef(addr, typ) when Memory.mostConcreteTypeOfHeapRef state addr typ = Types.String ->
                Memory.readArrayIndex state addr [index] (Types.Char, 1, true)
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ReadStringChar state v index)) |> Merging.merge
            | _ -> internalfailf "Reading string char: expected reference, but got %O" reference
        let ReadStaticField state typ field = Memory.readStaticField state typ field
        let ReadDelegate state reference = Memory.readDelegate state reference

        let WriteLocalVariable state location value = Memory.writeStackLocation state location value
        let WriteSafe state reference value = Memory.writeSafe state reference value
        let WriteStructField structure field value = Memory.writeStruct structure field value
        let WriteClassField state reference field value =
            Memory.guardedStatedMap
                (fun state reference ->
                    match reference.term with
                    | HeapRef(addr, _) -> Memory.writeClassField state addr field value
                    | _ -> internalfailf "Writing field of class: expected reference, but got %O" reference)
                state reference
        let WriteArrayIndex state reference indices value =
            Memory.guardedStatedMap
                (fun state reference ->
                    match reference.term with
                    | HeapRef(addr, typ) ->
                        let (_, dim, _) as arrayType = Memory.mostConcreteTypeOfHeapRef state addr typ |> symbolicTypeToArrayType
                        assert(dim = List.length indices)
                        Memory.writeArrayIndex state addr indices arrayType value
                    | _ -> internalfailf "Writing field of class: expected reference, but got %O" reference)
                state reference
        let WriteStringChar state reference index value =
            Memory.guardedStatedMap
                (fun state reference ->
                    match reference.term with
                    | HeapRef(addr, typ) when Memory.mostConcreteTypeOfHeapRef state addr typ = Types.String ->
                        Memory.writeArrayIndex state addr index (Types.Char, 1, true) value
                    | _ -> internalfailf "Writing field of class: expected reference, but got %O" reference)
                state reference
        let WriteStaticField state typ field value = Memory.writeStaticField state typ field value

        let DefaultOf typ = makeDefaultValue typ

        let MakeSymbolicThis m = Memory.makeSymbolicThis m
        let MakeSymbolicValue source name typ = Memory.makeSymbolicValue source name typ

        let CallStackContainsFunction state funcId = CallStack.containsFunc state.stack funcId
        let CallStackSize state = CallStack.size state.stack
        let GetCurrentExploringFunction state = CallStack.getCurrentFunc state.stack

        let BoxValueType state term =
            let address, state = Memory.freshAddress state
            let reference = HeapRef (ConcreteHeapAddress address) Types.ObjectType
            reference, Memory.writeBoxedLocation state address term

        let InitializeStaticMembers state targetType =
            Memory.initializeStaticMembers state targetType

        let AllocateTemporaryLocalVariable state typ term =
            let tmpKey = TemporaryLocalVariableKey typ
            let ref = PrimitiveStackLocation tmpKey |> Ref
            ref, Memory.allocateOnStack state tmpKey term

        let AllocateDefaultClass state typ =
            Memory.allocateClass state typ

        let AllocateDefaultArray state lengths typ =
            let address, state = Memory.allocateArray state typ None lengths
            HeapRef address typ, state

        let AllocateVectorArray state length elementType =
            let address, state = Memory.allocateVector state elementType length
            HeapRef address (ArrayType(elementType, Vector)), state

        let AllocateDelegate state delegateTerm = Memory.allocateDelegate state delegateTerm

        let AllocateString string state = Memory.allocateString state string
        let AllocateEmptyString state length = Memory.allocateEmptyString state length

        let CopyArray state src srcIndex dst dstIndex length =
            match src.term, dst.term with
            | HeapRef(srcAddress, srcSightType), HeapRef(dstAddress, dstSightType) ->
                let srcType = Memory.mostConcreteTypeOfHeapRef state srcAddress srcSightType |> symbolicTypeToArrayType
                let dstType = Memory.mostConcreteTypeOfHeapRef state dstAddress dstSightType |> symbolicTypeToArrayType
                Copying.copyArray state srcAddress srcIndex srcType dstAddress dstIndex dstType length
            | _ -> internalfailf "Coping arrays: expected heapRefs, but got %O, %O" src dst

        let CopyStringArray state src srcIndex dst dstIndex length =
            match src.term, dst.term with
            | HeapRef(srcAddress, srcSightType), HeapRef(dstAddress, dstSightType) ->
                assert(Memory.mostConcreteTypeOfHeapRef state srcAddress srcSightType = Types.String)
                assert(Memory.mostConcreteTypeOfHeapRef state dstAddress dstSightType = Types.String)
                let stringArrayType = (Types.Char, 1, true)
                Copying.copyArray state srcAddress srcIndex stringArrayType dstAddress dstIndex stringArrayType length
            | _ -> internalfailf "Coping arrays: expected heapRefs, but got %O, %O" src dst

        let IsTypeInitialized state typ = Memory.isTypeInitialized state typ
        let Dump state = Memory.dump state

        let rec ArrayRank state arrayRef =
            match arrayRef.term with
            | HeapRef(addr, typ) -> Memory.mostConcreteTypeOfHeapRef state addr typ |> Types.rankOf |> makeNumber
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ArrayRank state v)) |> Merging.merge
            | _ -> internalfailf "Getting rank of array: expected ref, but got %O" arrayRef
        let rec ArrayLengthByDimension state arrayRef index =
            match arrayRef.term with
            | HeapRef(addr, typ) -> Memory.mostConcreteTypeOfHeapRef state addr typ |> symbolicTypeToArrayType |> Memory.readLength state addr index
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ArrayLengthByDimension state v index)) |> Merging.merge
            | _ -> internalfailf "reading array length: expected heap reference, but got %O" arrayRef
        let rec ArrayLowerBoundByDimension state arrayRef index =
            match arrayRef.term with
            | HeapRef(addr, typ) -> Memory.mostConcreteTypeOfHeapRef state addr typ |> symbolicTypeToArrayType |> Memory.readLowerBound state addr index
            | Union gvs -> gvs |> List.map (fun (g, v) -> (g, ArrayLowerBoundByDimension state v index)) |> Merging.merge
            | _ -> internalfailf "reading array lower bound: expected heap reference, but got %O" arrayRef

        let StringLength state strRef = Memory.lengthOfString state strRef
        let StringCtorOfCharArray state arrayRef dstRef =
            match dstRef.term with
            | HeapRef({term = ConcreteHeapAddress dstAddr} as address, typ) ->
                assert(Memory.mostConcreteTypeOfHeapRef state address typ = Types.String)
                Memory.guardedStatedMap (fun state arrayRef ->
                    match arrayRef.term with
                    | HeapRef(arrayAddr, typ) ->
                        assert(Memory.mostConcreteTypeOfHeapRef state arrayAddr typ = ArrayType(Types.Char, Vector))
                        Copying.copyCharArrayToString state arrayAddr dstAddr
                    | _ -> internalfailf "constructing string from char array: expected array reference, but got %O" arrayRef)
                    state arrayRef
            | HeapRef _
            | Union _ -> __notImplemented__()
            | _ -> internalfailf "constructing string from char array: expected string reference, but got %O" dstRef

        let ComposeStates state state' = Memory.composeStates state state'

        let Merge2States (s1 : state) (s2 : state) = Memory.merge2States s1 s2
        let Merge2Results (r1, s1 : state) (r2, s2 : state) = Memory.merge2Results (r1, s1) (r2, s2)
//            let pc1 = PC.squashPC state1.pc
//            let pc2 = PC.squashPC state2.pc
//            if pc1 = Terms.True && pc2 = Terms.True then __unreachable__()
//            __notImplemented__() : state
            //Merging.merge2States pc1 pc2 {state1 with pc = []} {state2 with pc = []}

