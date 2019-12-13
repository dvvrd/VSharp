namespace VSharp

open System
open System.Collections.Generic

type internal autoref<'key, 'value when 'key : not struct and 'key : equality and 'value : not struct>
            (tgt : 'key, parent : weakdict<'key, 'value>, deflt : 'key) =
    let r = WeakReference<'key> tgt
    let badHash = 666

    override x.GetHashCode() =
        parent.InvokeOrFree x hash badHash
    override x.Equals(other : obj) =
        match other with
        | :? autoref<'key, 'value> as other ->
            parent.InvokeOrFree x (fun this ->
            parent.InvokeOrFree other (fun other ->
                this.Equals(other)) false) false
        | _ -> false
    override x.ToString() =
        let tgt = ref deflt
        if r.TryGetTarget(tgt) then tgt.ToString()
        else "<Garbage collected>"
    member x.TryGetTarget result = r.TryGetTarget(result)

and public weakdict<'key, 'value when 'key : not struct and 'key : equality and 'value : not struct> () =

    static let defaultKey = Unchecked.defaultof<'key>
    let dict = Dictionary<autoref<'key,'value>, 'value WeakReference>()
    member private this.dict = dict

    member private this.Free key =
        //assert (this.dict.Remove key)
        ()

    member internal this.InvokeOrFree<'a> (key : autoref<'key,'value>) (alive : 'key -> 'a) (dead : 'a) : 'a =
        let target = ref defaultKey
        if key.TryGetTarget(target) then
            !target |> alive
        else
            this.Free key
            dead

    member internal x.Remove key =
        x.dict.Remove key

    member public this.Add(key : 'key, value : 'value) =
        let keyRef = autoref<'key,'value>(key, this, defaultKey)
        let valWeakRef = WeakReference<'value> value
        let valRef = ref valWeakRef
        if this.dict.TryGetValue(keyRef, valRef) then
            (!valRef).SetTarget(value)
        else
            this.dict.Add(keyRef, valWeakRef)

    member public this.TryGetValue (key : 'key, result : 'value ref) : bool =
        let keyRef = autoref<'key,'value>(key, this, defaultKey)
        let valRef = ref <| WeakReference<'value>(!result)
        let contains = this.dict.TryGetValue(keyRef, valRef)
        if contains then
            let fin = (!valRef).TryGetTarget(result)
            fin
        else false
