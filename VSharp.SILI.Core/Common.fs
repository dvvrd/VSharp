namespace VSharp.Core

open VSharp
open VSharp.Core.Types.Constructor

type SolverResult = Sat | Unsat | Unknown
type ISolver =
    abstract Solve : term -> SolverResult
    abstract SolvePathCondition : term -> term list -> SolverResult

module internal Common =
    let mutable private solver : ISolver option = None
    let configureSolver s = solver <- Some s
    let private solve term =
        match solver with
        | Some s -> s.Solve term
        | None -> Unknown
    let private solvePC term pc =
        match solver with
        | Some s -> s.SolvePathCondition term pc
        | None -> Unknown

// ------------------------------- Simplification -------------------------------

    let simplifyPairwiseCombinations = Propositional.simplifyPairwiseCombinations

    let simplifyConcreteBinary simplify mtd isChecked t x y xval yval _ _ state =
        simplify (Metadata.combine3 mtd x.metadata y.metadata) isChecked state t xval yval

    let rec simplifyGenericUnary name state x matched concrete unmatched =
        match x.term with
        | Error _ -> matched (x, state)
        | Concrete(xval, typeofX) -> concrete x xval typeofX state |> matched
        | GuardedValues(guards, values) ->
            Cps.List.mapFoldk (fun state term matched -> simplifyGenericUnary name state term matched concrete unmatched) state values (fun (values', state) ->
                (Merging.merge (List.zip guards values'), state) |> matched)
        | _ -> unmatched x state matched

    let rec simplifyGenericBinary _ state x y matched concrete unmatched repeat =
        match x.term, y.term with
        | Error _, _ -> matched (x, state)
        | _, Error _ -> matched (y, state)
        | Concrete(xval, typeOfX), Concrete(yval, typeOfY) -> concrete x y xval yval typeOfX typeOfY state |> matched
        | Union(gvsx), Union(gvsy) ->
            let compose (gx, vx) state (gy, vy) matched = repeat vx vy state (fun (xy, state) -> ((gx &&& gy, xy), state) |> matched)
            let join state (gx, vx) k = Cps.List.mapFoldk (compose (gx, vx)) state gvsy k
            Cps.List.mapFoldk join state gvsx (fun (gvss, state) -> (Merging.merge (List.concat gvss), state) |> matched)
        | GuardedValues(guardsX, valuesX), _ ->
            Cps.List.mapFoldk (fun state x matched -> repeat x y state matched) state valuesX (fun (values', state) ->
            (Merging.merge (List.zip guardsX values'), state) |> matched)
        | _, GuardedValues(guardsY, valuesY) ->
            Cps.List.mapFoldk (fun state y matched -> repeat x y state matched) state valuesY (fun (values', state) ->
            (Merging.merge (List.zip guardsY values'), state) |> matched)
        | _ -> unmatched x y state matched

// ------------------------------- Type casting -------------------------------

    // TODO: support composition for this constant source
    [<StructuralEquality;NoComparison>]
    type private symbolicSubtypeSource =
        {left : termType; right : termType}
        interface ISymbolicConstantSource with
            override x.SubTerms = Seq.empty

    let (|SymbolicSubtypeSource|_|) (src : ISymbolicConstantSource) =
        match src with
        | :? symbolicSubtypeSource as li -> Some(li.left, li.right)
        | _ -> None

    let rec is metadata leftType rightType =
        let subtypeName lname rname = sprintf  "(%s <: %s)" lname rname
        let makeBoolConst lname rname leftTermType rightTermType =
            Constant metadata (subtypeName lname rname) ({left = leftTermType; right = rightTermType} : symbolicSubtypeSource) Bool
        match leftType, rightType with
        | _ when leftType = rightType -> makeTrue metadata
        | termType.Null, _
        | Void, _   | _, Void
        | Bottom, _ | _, Bottom -> makeFalse metadata
        | Reference _, Reference _ -> makeTrue metadata
        | Pointer _, Pointer _ -> makeTrue metadata
        | Func _, Func _ -> makeTrue metadata
        | ArrayType _ as t1, (ArrayType(_, SymbolicDimension name) as t2) ->
            if name = "System.Array" then makeTrue metadata else makeBoolConst (t1.ToString()) (t2.ToString()) t1 t2
        | ArrayType(_, SymbolicDimension _) as t1, (ArrayType _ as t2)  when t1 <> t2 ->
            makeBoolConst (t1.ToString()) (t2.ToString()) t1 t2
        | ArrayType(t1, ConcreteDimension d1), ArrayType(t2, ConcreteDimension d2) ->
            if d1 = d2 then is metadata t1 t2 else makeFalse metadata
        | TypeVariable(Implicit (_, t)) as t1, t2 ->
            is metadata t t2 ||| makeBoolConst (t1.ToString()) (t2.ToString()) t1 t2
        | t1, (TypeVariable(Implicit (_, t)) as t2) ->
            is metadata t1 t &&& makeBoolConst (t1.ToString()) (t2.ToString()) t1 t2
        | ConcreteType lt as t1, (ConcreteType rt as t2) ->
            if lt.Is rt then makeTrue metadata
            elif lt.IsGround && rt.IsGround then makeFalse metadata
            else makeBoolConst (t1.ToString()) (t2.ToString()) t1 t2
        | _ -> makeFalse metadata

    // TODO: support composition for this constant source
    [<StructuralEquality;NoComparison>]
    type private IsValueTypeConstantSource =
        {termType : termType}
        interface ISymbolicConstantSource with
            override x.SubTerms = Seq.empty

    let internal isValueType metadata termType =
        let makeBoolConst name = Constant metadata (sprintf "IsValueType(%s)" name) ({termType = termType} : IsValueTypeConstantSource) Bool
        match termType with
        | ConcreteType t when t.Inheritor.IsValueType -> makeTrue metadata
        | TypeVariable(Implicit(name, t)) ->
            if (Types.toDotNetType t).IsValueType
                then makeBoolConst name
                else makeFalse metadata
        | _ -> makeFalse metadata

// ------------------------------- Branching -------------------------------

    let statelessConditionalExecution conditionInvocation thenBranch elseBranch merge merge2 k =
        let execution condition k =
            thenBranch (fun thenResult ->
            elseBranch (fun elseResult ->
            k <| merge2 condition !!condition thenResult elseResult))
        conditionInvocation (fun condition ->
        match condition with
        | Terms.True ->  thenBranch k
        | Terms.False -> elseBranch k
        | Terms.ErrorT _ -> k condition
        | UnionT gvs -> Merging.commonGuardedMapk execution gvs merge k
        | _ ->
            match solve condition with
            | Unsat -> elseBranch k
            | _ ->
                match solve (!!condition) with
                | Unsat -> thenBranch k
                | _ -> execution condition k)

    let statedConditionalExecution (state : state) conditionInvocation thenBranch elseBranch merge merge2 errorHandler k =
        let execution conditionState condition k =
            thenBranch (State.withPathCondition conditionState condition) (fun (thenResult, thenState) ->
            elseBranch (State.withPathCondition conditionState !!condition) (fun (elseResult, elseState) ->
            let result = merge2 condition !!condition thenResult elseResult
            let state = Merging.merge2States condition !!condition (State.popPathCondition thenState) (State.popPathCondition elseState)
            k (result, state)))
        conditionInvocation state (fun (condition, conditionState) ->
        let thenCondition =
            Propositional.conjunction condition.metadata (condition :: State.pathConditionOf conditionState)
            |> Merging.unguard |> Merging.merge
        let elseCondition =
            Propositional.conjunction condition.metadata (!!condition :: State.pathConditionOf conditionState)
            |> Merging.unguard |> Merging.merge
        match thenCondition, elseCondition, condition with
        | False, _, _ -> elseBranch conditionState k
        | _, False, _ -> thenBranch conditionState k
        | _, _, (Terms.ErrorT _ as e) -> k (errorHandler e, conditionState)
        | _, _, UnionT gvs -> Merging.commonGuardedErroredMapk execution errorHandler gvs conditionState merge k
        | _ ->
            match solvePC condition (State.pathConditionOf conditionState) with
            | Unsat -> elseBranch conditionState k
            | _ ->
                match solve (!!condition) with
                | Unsat -> thenBranch conditionState k
                | _ -> execution conditionState condition k)
