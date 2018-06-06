namespace VSharp

open VSharp.Core

type foRelation =
    { id : string; signature : termType list } with
    override x.ToString() = x.id
type soRelation =
    { foRel : foRelation; relArgs : termType list list } with
    override x.ToString() = x.foRel.id

type relArg =
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

type foRelationalApplication =
    { symbol : foRelation; args : term list } with
    override x.ToString() =
        let args = x.args |> List.map toString |> join ", "
        sprintf "%s(%s)" x.symbol.id args

type soRelationalApplication =
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

type FOCHC = foRelationalApplication CHC
type SOCHC = soRelationalApplication CHC

type 'a CHCSystem = 'a list
type FOCHCSystem = FOCHC CHCSystem
type SOCHCSystem = SOCHC CHCSystem

module CHCs =

    let dump chcs = chcs |> List.map toString |> join "\n\n"

    let private soRel2FoRel (rel : soRelation) =
        if not rel.relArgs.IsEmpty then __notImplemented__()
        assert(rel.relArgs.IsEmpty)
        rel.foRel

    let private app2FO (soapp : soRelationalApplication) : foRelationalApplication =
        { symbol = soRel2FoRel soapp.symbol; args = soapp.args }

    let private chc2FO (sochc : SOCHC) : FOCHC =
        { constraints = sochc.constraints; body = List.map app2FO sochc.body; head = Option.map app2FO sochc.head }

    let toFirstOrder (sys : SOCHCSystem) : FOCHCSystem =
        List.map chc2FO sys
