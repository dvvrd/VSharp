namespace VSharp

open Microsoft.Z3
open VSharp.Core

type public ISolver<'TAst, 'TResult> =
    abstract member Solve : term list -> 'TResult

type public ISmtSolver<'TAst> =
    inherit ISolver<'TAst, SmtResult>

type public IZ3Solver =
    inherit ISmtSolver<AST>

type public Z3Solver() =
    let rec hasRecursiveCall t = // TODO: [encoding] temporary hack
        match t.term with
        | Concrete _ -> false
        | Constant(_, source, _) ->
            match source with
            | RecursionOutcome(_, _, Some _, _) -> true
            | _ -> false
        | Expression(_, ts, _) -> haveRecursiveCall ts
        | _ -> internalfailf "%O" t
    and haveRecursiveCall = List.exists hasRecursiveCall

    interface IZ3Solver with
        member x.Solve terms =
            if haveRecursiveCall terms then SmtUnknown null
            else
                try
                    let hochcs = Encode.encodeQuery terms
                    let chcs = CHCs.toFirstOrder hochcs
                    Z3.solve chcs
                with
                    | e when e.ToString().Contains("Database") ->
                        Logger.error "Exception during encoding! %O" e.Message
                        SmtSat null

type public Z3Simplifier() =
    interface IPropositionalSimplifier with
        member x.Simplify t = Z3.simplifyPropositional t

type public SmtSolverWrapper<'TAst>(solver : ISmtSolver<'TAst>) =
    interface VSharp.Core.ISolver with
        override x.Solve term =
            match solver.Solve [term] with
            | SmtSat _ -> VSharp.Core.Sat
            | SmtUnsat -> VSharp.Core.Unsat
            | SmtUnknown _ -> VSharp.Core.Unknown
        override x.SolvePathCondition term pc =
            // TODO: solving should be incremental!
            match solver.Solve (term::pc) with
            | SmtSat _ -> VSharp.Core.Sat
            | SmtUnsat -> VSharp.Core.Unsat
            | SmtUnknown _ -> VSharp.Core.Unknown
