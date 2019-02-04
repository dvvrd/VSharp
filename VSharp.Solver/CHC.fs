namespace VSharp

open System.Collections.Generic
open VSharp.Core

type internal emptySource =
    { id : string } with
    interface INonComposableSymbolicConstantSource with
        override x.SubTerms = seq[]

type internal foRelation =
    { id : string; signature : termType list } with
    override x.ToString() = x.id
type internal soRelation =
    { foRel : foRelation; relArgs : termType list list } with
    override x.ToString() = x.foRel.id

type internal relArg =
    | FoArg of foRelation
    | SoArg of soRelation * foRelation list * term list
    override x.ToString() =
        match x with
        | FoArg arg -> arg.id
        | SoArg(so, sos, fos) ->
            so.foRel.id::(List.append (sos |> List.map (fun f -> f.id)) (List.map toString fos)) |> join " " |> sprintf "[%s]"
    member x.Args =
        match x with
        | FoArg _ -> []
        | SoArg(_, _, args)-> args

type internal foRelationalApplication =
    { symbol : foRelation; args : term list } with
    override x.ToString() =
        let args = x.args |> List.map toString |> join ", "
        sprintf "%s(%s)" x.symbol.id args

type internal soRelationalApplication =
    { symbol : soRelation; relArgs : relArg list; args : term list } with
    override x.ToString() =
        let soArgs = x.relArgs |> List.map toString
        let foArgs = x.args |> List.map toString
        sprintf "%O(%s)" x.symbol (List.append soArgs foArgs |> join ", ")

type 'a CHC =
    { constraints : term list; body : 'a list; head : 'a option } with
    override x.ToString() =
        let head =
            match x.head with
            | Some app -> toString app
            | None -> "FALSE"
        let constraints = List.map toString x.constraints
        let apps = List.map toString x.body
        let body = List.append constraints apps
        sprintf "%s :- %s" head (join ", " body)

type internal FOCHC = foRelationalApplication CHC
type internal SOCHC = soRelationalApplication CHC

type internal 'a CHCSystem = 'a list
type internal FOCHCSystem = FOCHC CHCSystem
type internal SOCHCSystem = SOCHC CHCSystem

module CHCs =

    let dump chcs = chcs |> List.map toString |> join "\n\n"

    let rec private addArgClauses (argRelations : IDictionary<_, _>) (argClauses : IDictionary<_, List<FOCHC>>) (sorel : soRelation) relArgs =
        relArgs |> List.iteri (fun i arg ->
            let headRel = argRelations.[sorel, i]
            let headRelArgs = headRel.signature |> List.mapi (fun i -> let id = sprintf "$arg%d" i in Constant id {id = id})
            let headApp = { symbol = headRel; args = headRelArgs }
            // TODO: this is probably poor refinement typing! implement relatively complete algorithm
            let bodyApp =
                match arg with
                | FoArg rel -> { symbol = rel; args = headRelArgs; }
                | SoArg(rel, relArgs, args) ->
                    addArgClauses argRelations argClauses rel (List.map FoArg relArgs)
                    { symbol = rel.foRel; args = List.append args headRelArgs }
            let argClause = { constraints = []; body = [bodyApp]; head = Some headApp }
            argClauses.[sorel, i].Add(argClause))

    let private soApp2FO (argRelations : IDictionary<_, _>) (argClauses : IDictionary<_, _>) (soapp : soRelationalApplication) : foRelationalApplication =
        addArgClauses argRelations argClauses soapp.symbol soapp.relArgs
        { symbol = soapp.symbol.foRel; args = soapp.args }

    let private chc2FO (argRelations : IDictionary<_, _>) (argClauses : IDictionary<_, _>) (sochc : SOCHC) : FOCHC =
        let app2FO = soApp2FO argRelations argClauses
        { constraints = sochc.constraints; body = List.map app2FO sochc.body; head = Option.map (fun app -> { symbol = app.symbol.foRel; args = app.args }) sochc.head }

    let private initArgRelations (clauses : SOCHCSystem) =
        let argRelations = new Dictionary<soRelation * int, foRelation>()
        let argClauses = new Dictionary<soRelation * int, List<FOCHC>>()
        clauses |> List.iter (fun clause ->
            match clause.head with
            | Some head ->
                head.relArgs |> List.iteri (fun i -> function
                    | FoArg rel ->
                        let key = (head.symbol, i)
                        if not <| argRelations.ContainsKey key then
                            argRelations.Add(key, rel)
                            argClauses.Add(key, new List<FOCHC>())
                    | SoArg _ -> __unreachable__())
            | None -> ())
        argRelations, argClauses

    let toFirstOrder (sys : SOCHCSystem) : FOCHCSystem =
        let argRelations, argClauses = initArgRelations sys
        let clauses = List.map (chc2FO argRelations argClauses) sys
        argClauses.Values |> Seq.concat |> List.ofSeq |> List.append clauses
