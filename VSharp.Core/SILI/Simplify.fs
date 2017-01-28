﻿namespace VSharp.Core.Symbolic

open VSharp.Core.Symbolic
open VSharp.Core.Symbolic.Terms

module internal Simplify =

    let internal cons x xs = x :: xs
    let rec mapk f xs k = 
        match xs with
        | [] -> k []
        | x::xs' -> f x (fun y -> (mapk f xs' (k << cons y)))

    let rec internal simplifyGenericUnary name x matched concrete unmatched =
        match x with
        | Error _ -> matched x
        | Nop -> raise(new System.ArgumentException(sprintf "Invalid operand of %s!" name))
        | Concrete(x, typeofX) -> concrete x typeofX |> matched
        | GuardedValues(guards, values) -> // TODO: generic merge here?
            mapk (fun term matched -> simplifyGenericUnary name term matched concrete unmatched) values (fun values' ->
                Unions.make2 guards values' |> matched)
        | _ -> unmatched()

    let rec internal simplifyGenericBinary name x y matched concrete unmatched =
        match x, y with
        | Error _, _ -> matched x
        | _, Error _ -> matched y
        | Nop, _ -> raise(new System.ArgumentException(sprintf "Invalid left operand of %s!" name))
        | _, Nop -> raise(new System.ArgumentException(sprintf "Invalid right operand of %s!" name))
        | Concrete(x, typeOfX), Concrete(y, typeOfY) -> concrete x y typeOfX typeOfY |> matched
        | Union(gvsx), Union(gvsy) -> // TODO: generic merge here?
            let compose (gx, vx) (gy, vy) matched = simplifyGenericBinary name vx vy (fun gvxy -> (gx &&& gy, gvxy) |> matched) concrete unmatched in
                let join (gx, vx) k = mapk (compose (gx, vx)) gvsy k in
                    mapk join gvsx (List.concat >> Unions.make >> matched)
        | GuardedValues(guardsX, valuesX), _ -> // TODO: generic merge here?
            mapk (fun x matched -> simplifyGenericBinary name x y matched concrete unmatched) valuesX (fun values' ->
            Unions.make2 guardsX values' |> matched)
        | _, GuardedValues(guardsY, valuesY) -> // TODO: generic merge here?
            mapk (fun y matched -> simplifyGenericBinary name x y matched concrete unmatched) valuesY (fun values' ->
            Unions.make2 guardsY values' |> matched)
        | _ -> unmatched ()