namespace VSharp.System

open System.Collections.Generic
open global.System
open VSharp
open VSharp.Core
open ChessDotNet


// ------------------------------ System.Collections.Generic.ComparerHelpers --------------------------------

module EqualityComparer =

    let private createEqualityComparer state (typ : Type) =
        let genericEqualityComparer = typeof<EqualityComparer<_>>.Assembly.GetType("System.Collections.Generic.ObjectEqualityComparer`1")
        let genericEqualityComparer = genericEqualityComparer.MakeGenericType(typ)
        Types.FromDotNetType genericEqualityComparer |> Memory.AllocateDefaultClass state

    // TODO: now it works only for Piece! #do
    let internal CreateDefaultEqualityComparer (state : state) (args : term list) : term * state =
        assert(List.length args = 1)
        let runtimeType = List.head args
        let typ = Type.getActualType state runtimeType
        createEqualityComparer state typ

    let internal get_Default (state : state) (args : term list) : term * state =
        assert(List.length args = 0)
        let typ = typeof<Piece>
        createEqualityComparer state typ

    let internal get_DefaultForString (state : state) (args : term list) : term * state =
        assert(List.length args = 0)
        let typ = typeof<String>
        createEqualityComparer state typ

    let internal structuralEquality (state : state) block1 block2 =
        let block1Type = Terms.MostConcreteTypeOfHeapRef state block1
        let block2Type = Terms.MostConcreteTypeOfHeapRef state block2
        let checkContents () =
            let compareOneField acc (field, _) =
                let block1Field = Memory.ReadField state block1 field
                let block2Field = Memory.ReadField state block2 field
                block1Field === block2Field &&& acc
            let blockFields = Types.ToDotNetType block1Type |> Reflection.fieldsOf false
            Array.fold compareOneField True blockFields
        if block1Type <> block2Type then False // TODO: make this check symbolic #do
        else checkContents ()
