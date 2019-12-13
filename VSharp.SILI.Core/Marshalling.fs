namespace VSharp.Core
open System
open System.Collections.Generic
open System.Reflection
open FSharpx.Collections
open Types
open VSharp
open VSharp.CSharpUtils

#nowarn "69"

open VSharp.Core.Types.Constructor

module internal Marshalling =
    open Terms

    // very important mappings
    let physical2virtual = Dictionary<obj, term>(ReferenceEqualityComparer.Default)
    let virtual2physical = Dictionary<term, obj>()
    let isRegistered (o : obj) =
        physical2virtual.ContainsKey o
    let getPhysicalAddress (term : term) =
        virtual2physical.[term]
    let getVirtualTerm (o : obj) =
        physical2virtual.[o]

    let connect term obj =
        virtual2physical.Add(term, obj)
        physical2virtual.Add(obj, term)

    let disconnect term obj =
        let res1 = virtual2physical.Remove(term)
        let res2 = physical2virtual.Remove(obj)
        assert(res1 && res2)

    let clearMappings () =
        virtual2physical.Clear()
        physical2virtual.Clear()

    let isTypeInstance t = typedefof<System.Type>.IsAssignableFrom(t)
    let getTypeInstance (term : term) =
        match term.term with
        | Ref(RefTopLevelHeap(ConcreteT(t, _), _, _), _) -> t
        | _ -> __unreachable__()
    let rec createObjectOfType (t : System.Type) =
        match t with
        | _ when t.IsValueType -> Activator.CreateInstance t
        | _ ->
            let cctors = t.GetConstructors(Reflection.instanceBindingFlags)
            let ctor = Seq.fold (fun (acc : ConstructorInfo) (ctor : ConstructorInfo) ->
                if acc = null then ctor
                elif acc.GetParameters().Length < ctor.GetParameters().Length then acc else ctor) null cctors
            let arguments = ctor.GetParameters()
                            |> Seq.map (fun (parameterInfo : ParameterInfo) -> createObjectOfType parameterInfo.ParameterType)
                            |> Seq.toArray
            ctor.Invoke arguments

    let getFql ref fql =
        match fql with
        | Some _ -> fql
        | None ->
          match getFQLOfRef ref with
          | HeapTopLevelHeap(address, bt), path -> (HeapTopLevelHeap(address, bt), path) |> Some // in order to have right fql
          | x -> x |> Some

    // TODO: what if we have two symbolic objects each having reference to another?
    let marshal mtd state (term : term) =
        let rec bypass indexIsInt (reference : term option) (typ : termType option) term =
            let createBlock connect typ =
                let t = toDotNetType typ
                let obj = createObjectOfType t
                connect obj // to handle recursion references
                let allFields = Reflection.retrieveNonStaticFields t
                let marshalField field =
                    let name = Reflection.getFullNameOfField field
                    let typ = field.FieldType |> fromDotNetType
                    let value = Memory.readBlockField mtd term name typ
                    let fieldObj = bypass false None None value
                    field.SetValue(obj, fieldObj)
                FSharp.Collections.Array.iter marshalField allFields
                obj

            if virtual2physical.ContainsKey term then getPhysicalAddress term
            else
                let obj =
                    match term.term with
                    | _ when term = makeNullRef mtd -> null
                    | Concrete(obj, _) ->
                        if Option.isSome reference then connect (Option.get reference) obj
                        obj
                    | Struct(_, typ) ->
                        let connect =
                            match reference with
                            | Some reference -> connect reference
                            | None -> ignore
                        createBlock connect typ
                    | Class _ ->
                        let reference = Option.get reference
                        createBlock (connect reference) (baseTypeOfRef reference)
                    | Ptr _
                    | Ref _ ->
                        let typ = baseTypeOfRef term
                        let t = toDotNetType typ
                        if isTypeInstance t then
                            let obj = getTypeInstance term
                            connect term obj
                            obj
                        else
                            let value = Memory.derefWithoutValidation mtd state term
                            bypass false (Some term) (Some typ) value
                    | Array(d, _, bounds, _, contents, lengths) ->
                        let elementTyp = (Option.get typ) |> Types.elementType |> toDotNetType
                        let dims = bypass false None None d :?> int
                        let lowerBounds = FSharp.Collections.Array.init dims id
                        let lengthArray = FSharp.Collections.Array.init dims id
                        let f (array : int array) () (k : memoryCell<_, _, _>) v =
                            let index = bypass false None None k.key :?> int
                            let value = bypass false None None v :?> int
                            array.[index] <- value
                        Heap.fold (f lowerBounds) () bounds
                        Heap.fold (f lengthArray) () lengths

                        let array = System.Array.CreateInstance(elementTyp, lengthArray, lowerBounds)
                        let g () (indicesArray : memoryCell<_, _, _>) (v : term) =
                            let typ = typedefof<int[]> |> fromDotNetType |> Some
                            let value = bypass false None None v
                            if indexIsInt then
                                let index = bypass false None typ indicesArray.key :?> int
                                array.SetValue(value, index)
                            else
                                let indices = bypass true None typ indicesArray.key :?> int[]
                                array.SetValue(value, indices)
                        Heap.fold g () contents
                        if Option.isSome reference then connect (Option.get reference) array
                        array :> obj
                    | _ -> __unreachable__()
                obj
        bypass false None None term

    let canBeMarshalled mtd state (term : term) =
        let bypassedObjects = new HashSet<term>()
        let rec bypass (reference : term option) term =
            // TODO: what if we have two symbolic objects each having reference to another?
            let blockCase typ =
                let t = toDotNetType typ
                let allFields = Reflection.retrieveNonStaticFields t
                let fieldCanBeMarshaled field =
                    let name = Reflection.getFullNameOfField field
                    let typ = field.FieldType |> fromDotNetType
                    let value = Memory.readBlockField mtd term name typ
                    bypass None value
                FSharp.Collections.Array.forall fieldCanBeMarshaled allFields

            if bypassedObjects.Contains term then true
            else
                bypassedObjects.Add term |> ignore
                match term.term with
                | _ when term = makeNullRef mtd -> true
                | _ when isObject term -> false
                // TODO: add logic when Ref is [StackRef loc0] and loc0 is ConcreteValue!
                | Ref(address, path) when not <| isTopLevelHeapConcreteAddr (address.ConvertToHeapTopLevel(), path) ->
                    false
                | Ptr(address, path, _, _) when not <| isTopLevelHeapConcreteAddr (address.ConvertToHeapTopLevel(), path) ->
                    false
                | Concrete _ ->
                    true
                | Nop
                | Constant _
                | Expression _
                | Error _ ->
                    false
                | Union gvs ->
                    List.forall (fun (_, v) -> bypass reference v) gvs
                | Struct(_, typ) -> blockCase typ
                | Class _ ->
                    let typ = baseTypeOfRef (Option.get reference)
                    blockCase typ
                | Ptr _
                | Ref _ ->
                    let typ = typeOf term
                    let t = toDotNetType typ
                    if isTypeInstance t then true
                    else
                        let value = Memory.derefWithoutValidation mtd state term
                        bypass (Some term) value
                | Array(d, l, bs, insts, contents, lengths) ->
                    let acc0 = bypass None d
                    let acc1 = bypass None l
                    let acc2 = bs |> Seq.forall (fun (_, v) -> bypass None v)
                    let acc3 = insts |> List.map snd |> List.forall (function
                         | DefaultInstantiator _ -> true
                         | _ -> false)
                    let acc4 = contents |> Seq.forall (fun (_, v) -> bypass None v)
                    let acc5 = lengths |> Seq.forall (fun (_, v) -> bypass None v)
                    acc0 && acc1 && acc2 && acc3 && acc4 && acc5
        bypass None term

    let unmarshal fql mtd state (obj : obj) =
        let bypassedObjects = new HashSet<obj>()
        let rec helper state fql (obj : obj) =
            let t = if obj = null then null else obj.GetType()
            match obj with
            | null -> makeNullRef mtd, state
            | :? System.ValueType as value when t.IsPrimitive || t.IsEnum ->
                let t = value.GetType()
                let typ = fromDotNetType t
                let value = Concrete mtd value typ
                value, state
            | _ when bypassedObjects.Contains obj -> getVirtualTerm obj, state
            | :? System.ValueType ->
                let typ = fromDotNetType t
                let fieldsHeap, state =
                    Memory.mkFieldsForUnmarshaling mtd state (fun mtd state name _ fql' ->
                        let fields = Reflection.retrieveNonStaticFields t
                        let fieldInfo = fields |> Seq.find (fun f -> Reflection.getFullNameOfField f = name)
                        let value = fieldInfo.GetValue(obj)
                        helper state fql' value) fql typ
                let contents = Struct mtd fieldsHeap typ
                contents, state
            | _ ->
                bypassedObjects.Add obj |> ignore
                let typ = fromDotNetType t
                let freshAddress, fql =
                    if isRegistered obj then
                        Nop, getFql (physical2virtual.[obj]) fql
                    else
                        let fa =
                            if isTypeInstance t then
                                Concrete mtd obj (Constructor.fromDotNetType t) // addresses of Type instances are objects
                            else Memory.freshHeapLocation mtd
                        let fql = makeTopLevelFQL HeapTopLevelHeap (fa, typ) // What if current fql is Some ????
                        let address = makeFQLRef mtd (Option.get fql)
                        connect address obj
                        fa, fql
                let contents, state =
                    match obj with
                    | :? System.Array as array ->
                        let lengthsByDimensions = List.init array.Rank (fun i -> array.GetUpperBound i - array.GetLowerBound i + 1)
                        let typ = array.GetType() |> fromDotNetType
                        let mkContents state (index : int list) =
                            let index = List.toArray index
                            let obj = array.GetValue index
                            helper state fql obj
                        Arrays.fromMkContents mtd state array.Rank typ lengthsByDimensions mkContents fql
                    | _ ->
                        let fieldsHeap, state =
                            Memory.mkFieldsForUnmarshaling mtd state (fun mtd state name _ fql' ->
                                let fields = Reflection.retrieveNonStaticFields t
                                let fieldInfo = fields |> Seq.find (fun f -> Reflection.getFullNameOfField f = name)
                                let value = fieldInfo.GetValue(obj)
                                helper state fql' value) fql typ
                        let contents =
                            if t.IsValueType then Struct mtd fieldsHeap typ
                            else Class mtd fieldsHeap
                        contents, state
                if isRegistered obj then
                    let address = getVirtualTerm obj
                    let _, newState = Memory.mutate mtd state address contents
                    address, newState
                else
                    let address, state = Memory.allocateInHeap mtd state freshAddress typ typ contents
                    address, state
        if obj = null || not (obj.GetType().IsValueType) then helper state None obj
        else helper state fql obj

    let unmarshalUnknownLocation mtd state obj = unmarshal None mtd state obj

    type termForTypeOrigin =
        | GetType of term
        | TypeOf  of termType

    //    [<StructuralEquality;NoComparison>]
    type internal getTypeConstantSource =
        {origin : termForTypeOrigin}
        interface IStatedSymbolicConstantSource with
            override x.SubTerms = Seq.empty
    let getTypeMethod metadata state (term : term) =
        assert (isRef term)
        let makeGetTypeConstantSource term =
            let typ = typedefof<System.Type> |> Constructor.fromDotNetType
            let address = Constant metadata (sprintf "GetType(%O)" term) {origin = GetType term} typ // TODO: check typedefof<System.Type>
            Ref metadata (RefTopLevelHeap(address, typ, typ)) []
        match term.term with
        | Ref(RefTopLevelHeap(ConcreteT(:? System.Type as t, _), _, _), _) -> unmarshalUnknownLocation metadata state t
        | Ref(RefTopLevelHeap(ConcreteT(_, _), bt, _), _) ->
            let t = toDotNetType bt
            if t.IsGenericType then makeGetTypeConstantSource term, state
            else unmarshalUnknownLocation metadata state t
        | _ -> makeGetTypeConstantSource term, state

    let typeOfMethod metadata state (typ : termType) =
        let makeGetTypeConstantSource typ =
            let address = Constant metadata (sprintf "TypeOf(%O)" typ) {origin = TypeOf typ} (typedefof<System.Type> |> Constructor.fromDotNetType) // TODO: check typedefof<System.Type>
            Ref metadata (RefTopLevelHeap(address, typ, typ)) []
        let t = toDotNetType typ
        if t.IsGenericType then makeGetTypeConstantSource typ, state
        else unmarshalUnknownLocation metadata state t
    type getTypeConstantSource with
        interface IStatedSymbolicConstantSource with
            override x.Compose ctx state =
                match x.origin with
                | GetType term ->
                    let term = State.fillHoles ctx state term
                    getTypeMethod ctx.mtd state term |> fst // TODO: check it
                | TypeOf typ ->
                    let typ' = State.substituteTypeVariables ctx state typ
                    typeOfMethod ctx.mtd state typ' |> fst // TODO: check it


    let canBeCalledViaReflection mtd state (funcId : IFunctionIdentifier) this parameters =
        let canBeMarshalled = canBeMarshalled mtd state
        match this, parameters with
        | _, Unspecified -> false
        | None, _ when (funcId.Method :? ConstructorInfo) -> false
        | None, Specified args -> List.fold (fun acc arg -> acc && canBeMarshalled arg) true args
        | Some this, Specified args when funcId.IsConstructor ->
            let t = typeOf this |> toDotNetType
            List.fold (fun acc arg -> acc && canBeMarshalled arg) (t = funcId.Method.DeclaringType) args
        | Some this, Specified args -> List.fold (fun acc arg -> acc && canBeMarshalled arg) (canBeMarshalled this) args
        | _ -> false

    let callViaReflection mtd state (funcId : IFunctionIdentifier) (this : term option) (parameters : term list symbolicValue) k =
        Logger.trace "Calling concrete %O" funcId
        let k x =
            if physical2virtual.Count <> virtual2physical.Count then __unreachable__()
            clearMappings()
            k x

        clearMappings()
        let marshaledArgs =
            match parameters with
            | Specified args ->
                let marshaledArgs =
                    List.map (marshal mtd state) args
                    |> List.toSeq
                    |> Seq.zip (funcId.Method.GetParameters())
                    |> Seq.map (fun (p : ParameterInfo, obj : obj) -> if p.ParameterType.IsPrimitive && obj.GetType() <> p.ParameterType then Convert.ChangeType(obj, p.ParameterType) else obj)
                marshaledArgs |> Seq.toArray
            | _ -> __unreachable__()

        let resultObj, isResultVoid, state =
            match funcId.Method, this with
            | :? ConstructorInfo as ctor, Some this ->
                let constructedObj = ctor.Invoke(marshaledArgs)
                connect this constructedObj
                constructedObj, false, state
            | :? ConstructorInfo, None -> __unreachable__()
            | :? MethodInfo as method, None ->
                funcId.Method.Invoke(null, marshaledArgs), method.ReturnType = typedefof<Void>, state
            | :? MethodInfo as method, Some this ->
                let marshaledThis = marshal mtd state this
                let resultObj = method.Invoke(marshaledThis, marshaledArgs)
                let state = unmarshalUnknownLocation mtd state marshaledThis |> snd
                Logger.error "type of result = %O" (method.ReturnType)
                resultObj, method.ReturnType = typedefof<Void>, state
            | m -> internalfailf "Expected ConstructorInfo or MethodInfo, but got %O" <| m.GetType()
        let state = Seq.fold (fun state obj -> unmarshalUnknownLocation mtd state obj |> snd) state marshaledArgs
        if isResultVoid then k (Nop, state)
        else
            let fqlForValueTypeOnStack = Some (HeapTopLevelStack (SymbolicThisKey funcId.Method), [])
            // TODO: allocate in heap value types when Method.ReturnType is reference type
            let res, state = unmarshal fqlForValueTypeOnStack mtd state resultObj
            let res = Seq.fold (fun res obj -> if obj = resultObj && physical2virtual.ContainsKey obj
                                               then physical2virtual.[obj]
                                               else res) res marshaledArgs
            k (res, state)
