namespace VSharp

open JetBrains.Decompiler.Ast
open Microsoft.Z3
open System.Collections.Generic
open VSharp.Core
open Logger

module internal Z3 =

// ------------------------------- Cache -------------------------------

    type private relation = foRelation
    type private relationalApplication = foRelationalApplication
    type private CHC = FOCHC
    type private CHCSystem = FOCHCSystem

    type private encodingCache = {
        sorts : IDictionary<termType, Sort>
        e2t : IDictionary<Expr, term>
        t2e : IDictionary<term, Expr>
        relationSymbols : IDictionary<relation, FuncDecl>
        rules : IDictionary<IFunctionIdentifier, BoolExpr seq>
        mutable boundVarId : uint32
    } with
        member x.Get term encoder =
            Dict.tryGetValue2 x.t2e term (fun () ->
                let result = encoder()
                x.e2t.[result] <- term
                x.t2e.[term] <- result
                result)

    let private freshCache () = {
        sorts = new Dictionary<termType, Sort>()
        e2t = new Dictionary<Expr, term>()
        t2e = new Dictionary<term, Expr>()
        relationSymbols = new Dictionary<relation, FuncDecl>()
        rules = new Dictionary<IFunctionIdentifier, BoolExpr seq>()
        boundVarId = 0u
    }

    type private EncodingContext() as this =
        inherit Context()
        let cache = freshCache()
        let fp = this.MkFixedpoint()
        member x.Cache = cache
        member x.FP = fp

    let private ctxs = new System.Collections.Generic.Stack<EncodingContext>()
    let private ctx() = ctxs.Peek()

    let private freshBoundVar sort =
        (ctx()).Cache.boundVarId <- (ctx()).Cache.boundVarId + 1u
        (ctx()).MkBound((ctx()).Cache.boundVarId, sort)

// ------------------------------- Encoding: primitives -------------------------------

    let private validateId id =
        assert(not <| System.String.IsNullOrWhiteSpace id)
        if System.Char.IsDigit id.[0] then "_" + id else id

    let private type2Sort typ =
        Dict.getValueOrUpdate (ctx()).Cache.sorts typ (fun () ->
            match typ with
            | Bool -> (ctx()).MkBoolSort() :> Sort
            | Numeric _ as t when Types.IsInteger t -> (ctx()).MkIntSort() :> Sort
            | Numeric _ as t when Types.IsReal t -> (ctx()).MkRealSort() :> Sort
            | Numeric t -> (ctx()).MkEnumSort(t.FullName, t.GetEnumNames()) :> Sort
            | Reference _
            | Pointer _ -> (ctx()).MkIntSort() :> Sort // TODO
            | ArrayType _
            | Func _
            | Void
            | Bottom
            | Null
            | StructType _
            | ClassType _
            | InterfaceType _
            | TypeVariable _ -> __notImplemented__())

    let private encodeConcrete (obj : obj) typ =
        match typ with
        | Bool -> (ctx()).MkBool(obj :?> bool) :> Expr
        | Numeric t when t = typeof<char> -> (ctx()).MkNumeral(System.Convert.ToInt32(obj :?> char) |> toString, type2Sort typ)
        | Numeric t when t.IsEnum ->
            let sort = type2Sort typ :?> EnumSort in
            let name = obj.ToString() in
            FSharp.Collections.Array.find (toString >> ((=) name)) sort.Consts
        | Numeric _ ->
            match obj with
            | :? concreteHeapAddress as addr ->
                match addr with
                | [addr] -> (ctx()).MkNumeral(addr.ToString(), type2Sort typ)
                | _ -> __notImplemented__()
            | _ -> (ctx()).MkNumeral(obj.ToString(), type2Sort typ)
        | _ -> __notImplemented__()

    let private encodeConstant name typ term =
        ignore name
        (ctx()).Cache.Get term (fun () -> freshBoundVar(type2Sort typ))
//        cache.Get term (fun () -> (ctx()).MkConst(validateId name, type2Sort typ))

    let rec private encodeExpression stopper term op args typ =
        (ctx()).Cache.Get term (fun () ->
            match op with
            | Operator(operator, _) ->
                if stopper operator args then
                    let name = IdGenerator.startingWith "%tmp"
                    encodeConstant name typ term
                else
                    match operator with
                    | OperationType.LogicalNeg -> makeUnary stopper (ctx()).MkNot args :> Expr
                    | OperationType.LogicalAnd -> (ctx()).MkAnd(encodeTerms stopper args) :> Expr
                    | OperationType.LogicalOr -> (ctx()).MkOr(encodeTerms stopper args) :> Expr
                    | OperationType.Equal -> makeBinary stopper (ctx()).MkEq args :> Expr
                    | OperationType.Greater -> makeBinary stopper (ctx()).MkGt args :> Expr
                    | OperationType.GreaterOrEqual -> makeBinary stopper (ctx()).MkGe args :> Expr
                    | OperationType.Less -> makeBinary stopper (ctx()).MkLt args :> Expr
                    | OperationType.LessOrEqual -> makeBinary stopper (ctx()).MkLe args :> Expr
                    | OperationType.Add -> (ctx()).MkAdd(encodeTerms stopper args) :> Expr
                    | OperationType.Multiply -> (ctx()).MkMul(encodeTerms stopper args) :> Expr
                    | OperationType.Subtract -> (ctx()).MkSub(encodeTerms stopper args) :> Expr
                    | OperationType.Divide -> makeBinary stopper (ctx()).MkDiv args :> Expr
                    | OperationType.Remainder -> makeBinary stopper (ctx()).MkRem args :> Expr
                    | OperationType.UnaryMinus -> makeUnary stopper (ctx()).MkUnaryMinus args :> Expr
                    | OperationType.Not -> makeUnary stopper (ctx()).MkNot args :> Expr
                    | OperationType.ShiftLeft
                    | OperationType.ShiftRight -> __notImplemented__()
                    | _ -> __notImplemented__()
            | Application id ->
                let decl =
                    match id with
                    | :? IMethodIdentifier -> __notImplemented__()
                    | :? IDelegateIdentifier -> __notImplemented__()
                    | :? StandardFunctionIdentifier as sf -> (ctx()).MkConstDecl(sf.Function |> toString |> IdGenerator.startingWith, type2Sort typ)
                    | _ -> __notImplemented__()
                (ctx()).MkApp(decl, encodeTerms stopper args)
            | Cast _ ->
                __notImplemented__())

    and private makeUnary<'a, 'b when 'a :> Expr and 'b :> Expr>
            (stopper : OperationType -> term list -> bool)
            (constructor : 'a -> 'b)
            (args : term list) : 'b =
        match args with
        | [x] -> constructor (encodeTermExt<'a> stopper x)
        | _ -> internalfail "unary operation should have exactly one argument"

    and private makeBinary<'a, 'b, 'c when 'a :> Expr and 'b :> Expr and 'c :> Expr>
            (stopper : OperationType -> term list -> bool)
            (constructor : 'a * 'b -> 'c)
            (args : term list) : 'c =
        match args with
        | [x; y] -> constructor(encodeTermExt<'a> stopper x, encodeTermExt<'b> stopper y)
        | _ -> internalfail "binary operation should have exactly two arguments"

    and private encodeTerms<'a when 'a :> Expr> (stopper : OperationType -> term list -> bool) (ts : term seq) : 'a array =
        ts |> Seq.map (encodeTermExt<'a> stopper) |> FSharp.Collections.Array.ofSeq

    and private encodeTermExt<'a when 'a :> Expr> (stopper : OperationType -> term list -> bool) (t : term) : 'a =
        match t.term with
        | Concrete(obj, typ) -> encodeConcrete obj typ :?> 'a
        | Constant(name, _, typ) -> encodeConstant name.v typ t :?> 'a
        | Expression(op, args, typ) -> encodeExpression stopper t op args typ :?> 'a
        | HeapRef(((tl, _), _), _, _, _) -> encodeTermExt stopper tl // TODO
        | _ -> __notImplemented__()

    let private encodeTerm<'a when 'a :> Expr> (t : term) : 'a =
        encodeTermExt<'a> (fun _ _ -> false) t

// ------------------------------- Encoding: clauses -------------------------------

    let private encodeApp (app : relationalApplication) =
        let decl = Dict.getValueOrUpdate ((ctx()).Cache.relationSymbols) app.symbol (fun () ->
            let domain = List.map type2Sort app.symbol.signature
            let decl = (ctx()).MkFuncDecl(app.symbol.id, Array.ofList domain, (ctx()).MkBoolSort())
            (ctx()).FP.RegisterRelation decl
            decl)
        let args = List.map encodeTerm app.args
        (ctx()).MkApp(decl, args) :?> BoolExpr

    let private encodeClause failRel (chc : CHC) =
        let constraints = List.map encodeTerm chc.constraints
        let body = List.map encodeApp chc.body
        let head =
            match chc.head with
            | Some head -> encodeApp head
            | None -> failRel
        (ctx()).MkImplies(List.append constraints body |> Array.ofList |> (ctx()).MkAnd, head)

    let private encodeSystem (chcs : CHCSystem) =
        let failRel =
            let decl = (ctx()).MkFuncDecl(IdGenerator.startingWith "fail", [||], (ctx()).MkBoolSort())
            (ctx()).FP.RegisterRelation decl
            (ctx()).MkApp(decl, [||]) :?> BoolExpr
        chcs |> List.iter (encodeClause failRel >> (ctx()).FP.AddRule)
        failRel

// ------------------------------- Decoding -------------------------------

    let rec private decodeExpr op t (expr : Expr) =
        Expression (Operator(op, false)) (expr.Args |> Seq.map decode |> List.ofSeq) t

    and private decodeBoolExpr op (expr : BoolExpr) =
        decodeExpr op Bool expr

    and decode (expr : Expr) =
        if (ctx()).Cache.e2t.ContainsKey(expr) then (ctx()).Cache.e2t.[expr]
        else
            match expr with
            | :? IntNum as i -> Concrete i.Int (Numeric typeof<int>)
            | :? RatNum as r -> Concrete (double(r.Numerator.Int) * 1.0 / double(r.Denominator.Int)) (Numeric typeof<int>)
            | :? BoolExpr as b ->
                if b.IsTrue then True
                elif b.IsFalse then False
                elif b.IsNot then decodeBoolExpr OperationType.LogicalNeg b
                elif b.IsAnd then decodeBoolExpr OperationType.LogicalAnd b
                elif b.IsOr then decodeBoolExpr OperationType.LogicalOr b
                elif b.IsEq then decodeBoolExpr OperationType.Equal b
                elif b.IsGT then decodeBoolExpr OperationType.Greater b
                elif b.IsGE then decodeBoolExpr OperationType.GreaterOrEqual b
                elif b.IsLT then decodeBoolExpr OperationType.Less b
                elif b.IsLE then decodeBoolExpr OperationType.LessOrEqual b
                else __notImplemented__()
            | _ ->
                __notImplemented__()


// ------------------------------- Solving, etc. -------------------------------

    let solve (system : CHCSystem) =
        let context = new EncodingContext()
        ctxs.Push(context)
        try
            printLog Trace "SOLVER: got CHC system:\n%O" (system |> List.map toString |> join "\n")
            let failRel = encodeSystem system
            let result = (ctx()).FP.Query(failRel)
            printLog Trace "SOLVER: got %O" result
            match result with
            | Status.SATISFIABLE -> printfn "CEX: %O" ((ctx()).FP.GetAnswer()); SmtSat null
            | Status.UNSATISFIABLE -> SmtUnsat
            | Status.UNKNOWN -> printLog Trace "SOLVER: reason: %O" <| (ctx()).FP.GetReasonUnknown(); SmtUnknown ((ctx()).FP.GetReasonUnknown())
            | _ -> __unreachable__()
        finally
            ctxs.Pop() |> ignore
            context.Dispose()

    let simplifyPropositional t =
        let stopper op args =
            match op with
            | OperationType.LogicalNeg
            | OperationType.LogicalAnd
            | OperationType.LogicalOr
            | OperationType.Equal when List.forall (TypeOf >> Types.IsBool) args ->
                false
            | _ -> true
        let encoded = encodeTermExt stopper t
        let simple = encoded.Simplify()
        let result = decode simple
        printLog Trace "SOLVER: simplification of %O   gave   %O" t result
        printLog Trace "SOLVER: on SMT level encodings are %O    and     %O" encoded simple
        result
