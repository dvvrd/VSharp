namespace VSharp.Core

#nowarn "69"

open VSharp
open VSharp.Core.State
open VSharp.Core.Types
open VSharp.Core.Types.Constructor
open System.Collections.Immutable

module internal Memory =
    open Terms

// ------------------------------- Primitives -------------------------------

    let private pointer = persistent<int>(always 0, id)
    let private timestamp = persistent<timestamp>(always Timestamp.zero, id)
    let freshAddress() =
        pointer.Mutate(pointer.Value + 1)
        pointer.Value
    let tick() =
        timestamp.Mutate(timestamp.Value |> Timestamp.inc)
        timestamp.Value
    let reset() =
        pointer.Reset()
        timestamp.Reset()
    let saveConfiguration() =
        pointer.Save()
        timestamp.Save()
    let restore() =
        pointer.Restore()
        timestamp.Restore()

    let npe mtd state = State.createInstance mtd typeof<System.NullReferenceException> [] state

    let private npeTerm mtd state _ =
        let exn, state = npe mtd state
        Error mtd exn, state

    let rec private referenceSubLocation location arrayTarget term =
        match term.term with
        | Error _ -> term
        | StackRef(var, path, None) -> StackRef term.metadata var (List.append path [location])
        | StaticRef(var, path, None) -> StaticRef term.metadata var (List.append path [location])
        | HeapRef((addr, path), t, _, Reference _) -> HeapRef term.metadata (addr, List.append path [location]) arrayTarget t (snd location)
        | Terms.GuardedValues(gs, vs) -> vs |> List.map (referenceSubLocation location arrayTarget) |> List.zip gs |> Union term.metadata
        | _ -> internalfailf "expected reference, but got %O" term

    let rec private diveIntoReference path arrayTarget typ term =
        match term.term with
        | Error _ -> term
        | StackRef(var, path', _) -> { term = termNode.StackRef(var, (List.append path' path), typ); metadata = term.metadata }
        | StaticRef(var, path', None) -> { term = termNode.StaticRef(var, (List.append path' path), typ); metadata = term.metadata }
        | HeapRef((addr, path'), t, _, Reference _) ->
            if List.isEmpty path then term else HeapRef term.metadata (addr, List.append path' path) arrayTarget t (List.last path |> snd)
        | Terms.GuardedValues(gs, vs) -> vs |> List.map (diveIntoReference path arrayTarget typ) |> List.zip gs |> Union term.metadata
        | _ -> internalfailf "expected reference, but got %O" term

    let referenceArrayLowerBound arrayRef (indices : term) =
        referenceSubLocation (indices, Arrays.lengthTermType) ArrayLowerBounds arrayRef

    let referenceArrayLength arrayRef (indices : term) =
        referenceSubLocation (indices, Arrays.lengthTermType) ArrayLengths arrayRef

// ------------------------------- Traversal -------------------------------

    let rec private foldHeapLocationsRec arrayTarget folder acc loc path heap =
        Heap.fold (fun acc subloc cell -> foldSubLocations arrayTarget folder acc loc (List.append path [(subloc, typeOf cell.value)]) cell) acc heap

    and private foldSubLocations arrayTarget folder acc loc path cell =
        match cell.value.term with
        | Struct(contents, _) ->
            foldHeapLocationsRec arrayTarget folder acc loc path contents
        | Array(_, _, lower, _, contents, lengths, _) ->
            let acc = foldHeapLocationsRec ArrayLowerBounds folder acc loc path lower
            let acc = foldHeapLocationsRec ArrayLengths folder acc loc path lengths
            foldHeapLocationsRec ArrayContents folder acc loc path contents
        | _ -> folder acc loc path arrayTarget cell

    and private foldHeapLocations folder acc heap =
        Heap.fold (fun acc loc cell -> foldSubLocations ArrayContents folder acc (loc, typeOf cell.value) [] cell) acc heap

    and private foldStackLocations folder acc stack =
        stackFold (fun acc loc cell -> foldSubLocations ArrayContents folder acc loc [] cell) acc stack

// ------------------------------- Instantiation (lazy & default) -------------------------------

    [<StructuralEquality;NoComparison>]
    type private lazyInstantiation =
        {location : term; heap : generalizedHeap option; extractor : TermExtractor}
        interface IExtractingSymbolicConstantSource with
            override x.SubTerms = Seq.singleton x.location
            override x.WithExtractor e = {x with extractor = e} :> IExtractingSymbolicConstantSource

    let (|LazyInstantiation|_|) (src : ISymbolicConstantSource) =
        match src with
        | :? lazyInstantiation as li -> Some(li.location, li.heap, li.extractor :? IdTermExtractor)
        | _ -> None

    let private isStaticLocation = function
        | StaticRef _ -> true
        | _ -> false

    let private mkStruct metadata time isStatic mkField dotNetType typ =
        let fields = Types.fieldsOf dotNetType isStatic
        let contents =
            fields
            |> FSharp.Collections.Array.fold (fun acc (name, typ) ->
                let key = Terms.makeConcreteString name metadata
                let value = mkField metadata name typ
                Heap.add key { value = value; created = time; modified = time } acc) Heap.empty
        Struct metadata contents typ

    let rec private defaultOf time metadata typ =
        match typ with
        | Bool -> makeFalse metadata
        | Numeric t when t.IsEnum -> CastConcrete (System.Activator.CreateInstance t) t metadata
        | Numeric t -> CastConcrete 0 t metadata
        | Reference t -> Terms.makeNullRef t metadata
        | ClassType _
        | ArrayType _
        | InterfaceType _ -> Terms.makeNullRef typ metadata
        | TypeVariable _ ->
            Common.statelessConditionalExecution
                (fun k -> k <| Common.isValueType metadata typ)
                (fun k -> k <| Struct metadata Heap.empty typ)
                (fun k -> k <| Terms.makeNullRef typ metadata)
                Merging.merge Merging.merge2Terms id
        | Func _ -> Terms.makeNullRef (fromDotNetType typedefof<System.Delegate>) metadata
        | StructType(dotNetType, _) ->
            mkStruct metadata time false (fun m _ t -> defaultOf time m t) dotNetType typ
        | Pointer typ -> Terms.makeNullPtr typ metadata
        | _ -> __notImplemented__()

    let mkDefault metadata typ =
        defaultOf (tick()) metadata typ

    let mkDefaultStruct metadata isStatic termType =
        let dnt = toDotNetType termType
        let time = tick()
        mkStruct metadata time isStatic (fun m _ t -> defaultOf time m t) dnt termType

    let private makeSymbolicHeapReference metadata time (source : IExtractingSymbolicConstantSource) name typ construct =
        let source' = source.WithExtractor(Pointers.HeapAddressExtractor())
        let constant = Constant metadata name source' pointerType
        construct metadata ((constant, typ), []) ArrayContents {v=time} typ

    let private makeSymbolicOveralArrayLength metadata (source : IExtractingSymbolicConstantSource) arrayName =
        Constant metadata (sprintf "|%s|" arrayName) (source.WithExtractor(Arrays.LengthExtractor())) Arrays.lengthTermType

    let private makeSymbolicArrayRank metadata (source : IExtractingSymbolicConstantSource) arrayName =
        Constant metadata ("RankOf_%s" + arrayName) (source.WithExtractor(Arrays.RankExtractor())) Arrays.lengthTermType

    let private makeSymbolicArrayLowerBound metadata time name location heap =
        match Options.ExplorationMode() with
        | TrustConventions -> defaultOf time metadata Arrays.lengthTermType
        | CompleteExploration ->
            Constant metadata name {location = location; heap = heap; extractor = IdTermExtractor()} Arrays.lengthTermType

    let private makeSymbolicArrayLength metadata name location heap =
        Constant metadata name {location = location; heap = heap; extractor = IdTermExtractor()} Arrays.lengthTermType

    let private makeSymbolicArrayLowerBounds metadata (source : IExtractingSymbolicConstantSource) arrayName dimension =
        match source with
        | :? lazyInstantiation as liSource ->
            match Options.ExplorationMode() with
            | TrustConventions -> Arrays.zeroLowerBound metadata dimension
            | CompleteExploration ->
                let idOfBound i = sprintf "%s.%i_LowerBound" arrayName i
                let mkLowerBound i = Constant metadata (idOfBound i) {liSource with location = referenceArrayLowerBound liSource.location (makeNumber i metadata)} Arrays.lengthTermType
                Seq.foldi (fun h i l -> Heap.add (makeNumber i metadata) { value = l; created = Timestamp.zero; modified = Timestamp.zero } h) Heap.empty (Seq.init dimension mkLowerBound)
        | _ -> __notImplemented__()

    let private makeSymbolicArrayLengths metadata (source : IExtractingSymbolicConstantSource) arrayName dimension =
        match source with
        | :? lazyInstantiation as liSource ->
            let idOfLength i = sprintf "%s.%i_Length" arrayName i
            let mkLength i = Constant metadata (idOfLength i) {liSource with location = referenceArrayLength liSource.location (makeNumber i metadata)} Arrays.lengthTermType
            let lengths = Seq.init dimension mkLength
            let length = Seq.reduce (mul metadata) lengths
            Seq.foldi (fun h i l -> Heap.add (makeNumber i metadata) { value = l; created = Timestamp.zero; modified = Timestamp.zero } h) Heap.empty lengths, length
        | _ -> __notImplemented__()

    let private makeSymbolicArray metadata (source : IExtractingSymbolicConstantSource) dimension elemTyp typ arrayName =
        let arrayConstant = Constant metadata arrayName source typ
        let instantiator = [True, LazyInstantiator(arrayConstant, elemTyp)]
        let lowerBound, arrayLengths, arrayLength, dim =
            let makeConcrete d =
                let lb = makeSymbolicArrayLowerBounds metadata source arrayName d
                let al, length = makeSymbolicArrayLengths metadata source arrayName d
                lb, al, length, makeNumber d metadata
            match dimension with
            | Vector -> makeConcrete 1
            | ConcreteDimension d -> makeConcrete d
            | SymbolicDimension _ ->
                let length = makeSymbolicOveralArrayLength metadata source arrayName
                Heap.empty, Heap.empty, length, makeSymbolicArrayRank metadata source arrayName
        Array metadata dim arrayLength lowerBound instantiator Heap.empty arrayLengths typ

    let makeSymbolicInstance metadata time (source : IExtractingSymbolicConstantSource) name = function
        | Pointer typ -> makeSymbolicHeapReference metadata time source name typ <| fun mtd path _ time typ -> HeapPtr mtd path time typ
        | Reference typ -> makeSymbolicHeapReference metadata time source name typ HeapRef
        | t when Types.isPrimitive t || Types.isFunction t -> Constant metadata name source t
        | StructType _ // TODO: initialize all fields of struct symbolicly (via mkStruct). Warning: `source` should be updated!
        | TypeVariable _
        | ClassType _ as t -> Struct metadata Heap.empty t
        | ArrayType(e, d) as t -> makeSymbolicArray metadata source d e t name
        | Void -> Nop
        | _ -> __notImplemented__()


    let private genericLazyInstantiator =
        let instantiator metadata heap time fullyQualifiedLocation typ () =
            makeSymbolicInstance metadata time {location = fullyQualifiedLocation; heap = heap; extractor = IdTermExtractor()} (nameOfLocation fullyQualifiedLocation) typ
        State.genericLazyInstantiator <- instantiator
        instantiator

    let private arrayElementLazyInstantiator metadata instantiator typ heap time location idx = function
        | DefaultInstantiator(_, concreteType) -> fun () -> defaultOf time metadata (typ |?? concreteType)
        | LazyInstantiator(array, concreteType) -> instantiator |?? fun () ->
            let id = sprintf "%s[%s]" (toString array) (idx.term.IndicesToString()) |> IdGenerator.startingWith
            makeSymbolicInstance metadata time {location = location; heap = heap; extractor = IdTermExtractor()} id (Types.Variable.fromTermType concreteType)

    let private arrayLowerBoundLazyInstantiator metadata instantiator _ heap time location (idx : term) = function
        | DefaultInstantiator(_, _) -> fun () -> defaultOf time metadata Arrays.lengthTermType
        | LazyInstantiator(array, _) -> instantiator |?? fun () ->
            let name = sprintf "%O.%s_LowerBound" array (idx.term.IndicesToString())
            makeSymbolicArrayLowerBound metadata time name location heap

    let private arrayLengthLazyInstantiator metadata instantiator _ heap _ location (idx : term) = function
        | DefaultInstantiator(_, _) -> fun () ->
            // In case when array was allocated during the interpretation (and thus has default instantiator) lengths by
            // all dimensions are known (they can be symbolic, but still defined). If this code triggers then we have
            // requested length by a greater dimension than our array has. That can happen in case of comparison of array
            // lengths when arrays have different ranks. In that case we consider lengths in all other dimensions equal to 1.
            makeNumber 1 metadata
        | LazyInstantiator(array, _) -> instantiator |?? fun () ->
            let name = sprintf "%O.%s_Length" array (idx.term.IndicesToString())
            makeSymbolicArrayLength metadata name location heap

    let private staticMemoryLazyInstantiator metadata t () =
        Struct metadata Heap.empty (fromDotNetType t)

    let private selectLazyInstantiator metadata heap time arrayTarget fullyQualifiedLocation typ =
        match arrayTarget with
        | ArrayLengths -> fun () -> makeSymbolicArrayLength metadata (nameOfLocation fullyQualifiedLocation + "_Length") fullyQualifiedLocation heap
        | ArrayLowerBounds -> fun () -> makeSymbolicArrayLowerBound metadata time (nameOfLocation fullyQualifiedLocation + "_LowerBound") fullyQualifiedLocation heap
        | _ -> genericLazyInstantiator metadata heap time fullyQualifiedLocation typ

// ------------------------------- Locations comparison -------------------------------

    type private pointerInfo = { location : term; fullyQualifiedLocation : term; typ : termType; time : timestamp; path : (term * termType) list; isTopLevel : bool; arrayTarget : arrayReferenceTarget }

    let private canPoint mtd pointerAddr pointerType pointerTime locationAddr locationValue locationTime =
        // TODO: what if locationType is Null?
        if locationTime > pointerTime then makeFalse mtd
        else
            let addrEqual = Pointers.locationEqual mtd locationAddr pointerAddr
            let typeSuits v =
                let locationType = typeOf v
                Common.is mtd locationType pointerType &&& Common.is mtd pointerType locationType
            let typeEqual =
                match locationValue.term with
                | Union gvs ->
                    gvs |> List.map (fun (g, v) -> (g, typeSuits v)) |> Merging.merge
                | _ -> typeSuits locationValue
            if isConcrete addrEqual then addrEqual else addrEqual &&& typeEqual

    let private findSuitableLocations mtd h mapper (ptr : pointerInfo) =
        let filterMapKey (k, cell) =
            let k = mapper k
            let cell = {cell with value = mapper cell.value}
            let guard = canPoint mtd ptr.location ptr.typ ptr.time k cell.value cell.created
            match guard with
            | False -> None
            | _ -> Some(guard, k, cell)
        let gvs = h |> Heap.toSeq |> List.ofSeq |> List.choose filterMapKey
        let baseGvs, restGvs = gvs |> List.partition (fst3 >> isTrue)
        assert(List.length baseGvs <= 1)
        List.tryHead baseGvs, restGvs

// ------------------------------- Primitive read/write -------------------------------

    let private stackDeref time instantiateLazy state location =
        if isAllocatedOnStack state location then
            (readStackLocation state location, state)
        else
            let lazyInstance = {value = instantiateLazy(); created = time; modified = time }
            (lazyInstance, writeStackLocation state location lazyInstance)

    let private writeHeap time guard h addr newValue =
        assert(Heap.contains addr h)
        let oldCell = Heap.find addr h
        let cell = Merging.merge2Cells guard !!guard { oldCell with value = newValue; modified = time } oldCell
        Heap.add addr cell h

// ------------------------------- Core -------------------------------

    let rec private accessTerm read metadata groundHeap guard update mapper lazyInstantiator created modified ptrTime ptrFql path arrayMode term =
        match path with
        | [] ->
            let newTerm, newTime = update term modified
            newTerm, newTerm, newTime
        | ((key, typ) as location)::path' ->
            match term.term with
            | Error _ -> term, term, modified
            | Struct(fields, t) ->
                let fql' = referenceSubLocation location arrayMode ptrFql
                let ptr' = {location = key; fullyQualifiedLocation = fql'; typ = typ; time = ptrTime; path = path'; isTopLevel = false; arrayTarget = arrayMode}
                let instantiator = if read then lazyInstantiator else genericLazyInstantiator term.metadata groundHeap modified fql' typ
                let result, newFields, newTime =
                    accessHeap read false metadata groundHeap guard update fields created mapper instantiator ptr'
                result, Struct term.metadata newFields t, newTime
            | Array(dimension, length, lower, constant, contents, lengths, arrTyp) ->
                let fql' = referenceSubLocation location arrayMode ptrFql
                let ptr' = {location = key; fullyQualifiedLocation = fql'; typ = typ; time = ptrTime; path = path'; isTopLevel = false; arrayTarget = arrayMode}
                let makeInstantiator key instantiator =
                    let realInstantiator = if read then Some lazyInstantiator else None
                    let targetType = if read then Some(path |> List.last |> snd) else None
                    let doJob = lazy(Merging.guardedMap (fun c -> instantiator term.metadata realInstantiator targetType groundHeap modified fql' key c ()) constant)
                    doJob.Force
                let newHeap heap instantiator = accessHeap read false metadata groundHeap guard update heap created mapper instantiator ptr'
                match arrayMode with
                | _ when arrayMode = ArrayContents || not (List.isEmpty path') ->
                    let instantiator = makeInstantiator key arrayElementLazyInstantiator
                    let result, newContents, newTime = newHeap contents instantiator
                    result, Array term.metadata dimension length lower constant newContents lengths arrTyp, newTime
                | ArrayLengths ->
                    let instantiator = makeInstantiator key arrayLengthLazyInstantiator
                    let result, newLengths, newTime = newHeap lengths instantiator
                    result, Array term.metadata dimension length lower constant contents newLengths arrTyp, newTime
                | ArrayLowerBounds ->
                    let instantiator = makeInstantiator key arrayLowerBoundLazyInstantiator
                    let result, newLower, newTime = newHeap lower instantiator
                    result, Array term.metadata dimension length newLower constant contents lengths arrTyp, newTime
                | _ -> __unreachable__()
            | Union _ ->
                internalfail "unexpected union of complex types! Probably merge function implemented incorrectly."
            | t ->
                internalfailf "expected complex type, but got %O" t

    and private accessHeap read restricted metadata groundHeap guard update h time mapper lazyInstantiator (ptr : pointerInfo) =
        let accessRec gvas lazyValue h =
            let gvs, (h', newTime) = gvas |> ((h, Timestamp.zero) |> List.mapFold (fun (h, maxTime) (guard', addr, cell) ->
                let guard'' = guard &&& guard'
                let accessedValue, newBaseValue, newTime = accessTerm read metadata groundHeap guard update mapper lazyInstantiator cell.created cell.modified ptr.time ptr.fullyQualifiedLocation ptr.path ptr.arrayTarget cell.value
                let h' = if read || cell.value = newBaseValue then h else writeHeap newTime guard'' h addr newBaseValue
                ((guard'', accessedValue), (h', max maxTime newTime))))
            (Merging.merge (optCons gvs lazyValue), h', newTime)
        if isConcrete ptr.location && Heap.contains ptr.location h then
            accessRec [(makeTrue metadata, ptr.location, Heap.find ptr.location h)] None h
        else
            let baseGav, restGavs = findSuitableLocations metadata h mapper ptr
            match baseGav with
            | None when read && restricted ->
                // TODO: undefined behaviour detected!
                __notImplemented__()
            | None ->
                let baseGuard = restGavs |> List.map (fst3 >> (!!)) |> conjunction metadata
                let shouldLazyInstantiate = read && not ptr.isTopLevel
                let lazyValue =
                    if ptr.isTopLevel then genericLazyInstantiator metadata groundHeap time ptr.fullyQualifiedLocation ptr.typ ()
                    else lazyInstantiator()
                let baseCell = { value = lazyValue; created = time; modified = time}
                let gavs = if shouldLazyInstantiate then restGavs else (baseGuard, ptr.location, baseCell)::restGavs
                let lv = if shouldLazyInstantiate then Some(baseGuard, lazyValue) else None
                let h = if shouldLazyInstantiate then h else h.Add(ptr.location, baseCell)
                accessRec gavs lv h
            | Some(g, a, v) -> accessRec ((g, a, v)::restGavs) None h

    let private commonHierarchicalStackAccess read update metadata state location path =
        let firstLocation = stackLocationToReference state location
        let time = frameTime state location
        let cell, _ = stackDeref time (fun () -> (stackLazyInstantiator state time location).value) state location
        let termLazyInstantiator = if read && not (List.isEmpty path) then genericLazyInstantiator metadata None time (StackRef metadata location path) (path |> List.last |> snd) else __unreachable__
        let accessedValue, newBaseValue, newTime = accessTerm read metadata None (makeTrue metadata) update id termLazyInstantiator cell.created cell.modified time firstLocation path ArrayContents cell.value
        let newState = if read || cell.value = newBaseValue then state else writeStackLocation state location { cell with value = newBaseValue; modified = newTime }
        accessedValue, newState

    let private commonHierarchicalHeapAccess read restricted update metadata groundHeap heap mapper lazyInstantiator ((addr, t) as location) path time arrayMode =
        let firstLocation = HeapRef metadata (location, []) arrayMode time t
        let typ' = if List.isEmpty path then t else path |> List.last |> snd
        let lazyInstantiator = lazyInstantiator |?? selectLazyInstantiator metadata groundHeap time.v arrayMode (HeapRef metadata (location, path) arrayMode time typ') typ'
        let ptr = {location = addr; fullyQualifiedLocation = firstLocation; typ = t; time = time.v; path = path; isTopLevel = true; arrayTarget = arrayMode}
        accessHeap read restricted metadata groundHeap (makeTrue metadata) update heap Timestamp.zero mapper lazyInstantiator ptr

    let private commonHierarchicalStaticsAccess read restricted update metadata groundHeap statics mapper lazyInstantiator location path =
        let addr = Terms.makeStringKey location
        let dnt = System.Type.GetType(location)
        let t = fromDotNetType dnt
        let lazyInstantiator = lazyInstantiator |?? genericLazyInstantiator metadata groundHeap Timestamp.zero (StaticRef metadata location path) (if path.IsEmpty then t else path |> List.last |> snd)
        let ptr = {location = addr; fullyQualifiedLocation = StaticRef metadata location []; typ = t; time = Timestamp.infinity; path = path; isTopLevel = true; arrayTarget = ArrayContents}
        accessHeap read restricted metadata groundHeap (makeTrue metadata) update statics Timestamp.zero mapper lazyInstantiator ptr

    let mutateStack metadata state location path time value =
        commonHierarchicalStackAccess false (fun _ _ -> (value, time)) metadata state location path

    let private mutateHeap restricted metadata h location path time arrayTarget value =
        commonHierarchicalHeapAccess false restricted (fun _  _ -> (value, time)) metadata None h id None location path {v=time} arrayTarget

    let private mutateStatics restricted metadata statics location path time value =
        commonHierarchicalStaticsAccess false restricted (fun _ _ -> (value, time)) metadata None statics id None location path

    let rec private independent (exploredRecursiveIds : ImmutableHashSet<IFunctionIdentifier>) (exploredLocations : ImmutableHashSet<term>) read funcId location : bool =
        exploredLocations.Contains(location) ||
        let exploredRecursiveIds = exploredRecursiveIds.Add funcId
        match Database.querySummary funcId with
        | Some summary ->
            let t, _ = read exploredRecursiveIds summary.state
            match t.term with
            | Constant(_, LazyInstantiation(location', None, true), _) when location = location' -> true
            |_ -> false
        | None -> false

    and private accessGeneralizedHeapRec (exploredIds : ImmutableHashSet<IFunctionIdentifier>) unlucky mapper lazyInstantiator read getter location accessDefined = function
        | Defined(r, h) ->
            let result, heap, _ = accessDefined mapper lazyInstantiator None r h
            result, Defined r heap
        | Merged ghs ->
            let gs, hs = List.unzip ghs
            let rs, hs' = hs |> List.map (accessGeneralizedHeapRec exploredIds unlucky mapper lazyInstantiator read getter location accessDefined) |> List.unzip
            let grs = List.zip gs rs
            Merging.merge grs, Merging.mergeGeneralizedHeaps gs hs'
        | Mutation(h, h') as m ->
            let result, h'', _ = accessDefined mapper lazyInstantiator (Some h) false h'
            if read then
                let accessH = lazy(accessGeneralizedHeapRec exploredIds unlucky mapper lazyInstantiator read getter location accessDefined h |> fst)
                let simplifyInstantiated term =
                    match term.term with
                    | Constant(_, LazyInstantiation(loc, Some heap, _), _) when loc = location && heap = h ->
                        accessH.Force()
                    | _ -> term
                Substitution.substitute simplifyInstantiated id result, m
            else
                result, Mutation(h, h'')
        | Composition(_, _, Defined _) ->
            internalfail "composition with the defined heap should not be met, it must be simplified to a simple mutation!"
        | Composition(s, ctx, h) as heap when read ->
            let mapper' = mapper >> fillHoles ctx s
            let unlucky _ = unlucky heap  // if simplification of 'h' fails then we should return 'heap' instead of 'h'
            let lazyInstantiator' = lazy(accessGeneralizedHeapRec exploredIds unlucky mapper lazyInstantiator read getter location accessDefined (getter s) |> fst)
            accessGeneralizedHeapRec exploredIds unlucky mapper' (Some lazyInstantiator'.Force) read getter location accessDefined h
        | RecursiveApplication(f, _, _) as h
                when not <| exploredIds.Contains(f) && read &&
                     independent exploredIds ImmutableHashSet.Empty
                                 (fun ids s -> accessGeneralizedHeapRec ids unlucky mapper lazyInstantiator read getter location accessDefined (getter s)) f location ->
            let r, _, _ = accessDefined mapper lazyInstantiator None false Heap.empty
            r, h
        | RecursiveApplication _
        | HigherOrderApplication _ as h -> unlucky h
        | _ -> __unreachable__()

    and private accessGeneralizedHeap read getter location accessDefined =
        let unlucky h =
            let r, e, _ = accessDefined id None (Some h) false Heap.empty
            r, if read then h else Mutation(h, e)
        accessGeneralizedHeapRec ImmutableHashSet.Empty unlucky id None read getter location accessDefined

    and private hierarchicalAccess validate read actionNull updateDefined metadata state term =
        match term.term with
        | Error _ -> (term, state)
        | StackRef(location, path, None) ->
            commonHierarchicalStackAccess read updateDefined metadata state location path
        | HeapRef(((addr, t) as location, path), time, arrayMode, Reference _) ->
            let doRead state k =
                let accessDefined mapper lazyInstantiator groundHeap r h =
                    commonHierarchicalHeapAccess read r updateDefined metadata groundHeap h mapper lazyInstantiator location path time arrayMode
                let result, h' = accessGeneralizedHeap read heapOf term accessDefined (heapOf state)
                k (result, withHeap state h')
            if validate then
                Common.statedConditionalExecution state
                    (fun state k -> k (Arithmetics.simplifyEqual metadata addr (Concrete metadata [0] pointerType) id, state))
                    (fun state k -> k (actionNull metadata state t))
                    doRead
                    Merging.merge Merging.merge2Terms id id
            else doRead state id
        | StaticRef(location, path, None) ->
            let accessDefined mapper lazyInstantiator groundHeap r h =
                commonHierarchicalStaticsAccess read r updateDefined metadata groundHeap h mapper lazyInstantiator location path
            let result, m' = accessGeneralizedHeap read staticsOf term accessDefined (staticsOf state)
            result, withStatics state m'
        | Union gvs -> Merging.guardedStateMap (hierarchicalAccess validate read actionNull updateDefined metadata) gvs state
        | PointerTo viewType ->
            let ref = getReferenceFromPointer metadata term
            let term, state = hierarchicalAccess validate read actionNull updateDefined metadata state ref
            if typeOf term = viewType
            then term, state
            else __notImplemented__() // TODO: [columpio] [Reinterpretation]
        | t -> internalfailf "expected reference or pointer, but got %O" t

// ------------------------------- Composition -------------------------------

    and private fillHole (ctx : compositionContext) state term =
        match term.term with
        | Constant(_, source, _) ->
            match source with
            | :? IStatedSymbolicConstantSource as source -> source.Compose ctx state
            | :? INonComposableSymbolicConstantSource -> term
            | _ -> __notImplemented__()
        | Concrete(:? concreteHeapAddress as addr', t) ->
            Concrete ctx.mtd (composeAddresses ctx.addr addr') t
        | Pointers.SymbolicThisOnStack(token, path, typ) ->
            let id = ("this", token)
            let reference = referenceLocalVariable term.metadata state id false |> deref term.metadata state |> fst
            diveIntoReference path ArrayContents typ reference
        | _ -> term

    and fillHoles ctx state term =
        Substitution.substitute (fillHole ctx state) (State.substituteTypeVariables state) term

    and fillHolesInHeap ctx state heap =
        Heap.map (fun k cell -> (fillHoles ctx state k, {cell with value = fillHoles ctx state cell.value})) heap

    and private fillAndMutateStack (ctx : compositionContext) source target loc path _ cell =
        let time = Timestamp.compose ctx.time cell.modified
        let path = path |> List.map (mapfst <| fillHoles ctx source)
        let v = fillHoles ctx source cell.value
        mutateStack ctx.mtd target loc path time v |> snd

    and private fillAndMutateHeap (ctx : compositionContext) restricted source target (addr, t) path arrayTarget cell =
        let time = Timestamp.compose ctx.time cell.modified
        let addr = fillHoles ctx source addr
        let loc = (addr, t)
        let path = path |> List.map (mapfst <| fillHoles ctx source)
        let v = fillHoles ctx source cell.value
        mutateHeap restricted ctx.mtd target loc path time arrayTarget v |> snd3

    and private fillAndMutateStatics (ctx : compositionContext) restricted source target (addr, _) path _ cell =
        let time = Timestamp.compose ctx.time cell.modified
        let addr = fillHoles ctx source addr
        let path = path |> List.map (mapfst <| fillHoles ctx source)
        let v = fillHoles ctx source cell.value
        let loc =
            match addr.term with
            | Concrete(s, StringType) -> string s
            | _ -> __notImplemented__()
        mutateStatics restricted ctx.mtd target loc path time v |> snd3

    and private composeDefinedHeaps writer restricted s h h' =
        foldHeapLocations (writer restricted s) h h'

    and private composeGeneralizedHeaps writer ctx getter setter s h' =
        match getter s, h' with
        | Defined(r, h), Defined(r', h') ->
            assert(not r')
            composeDefinedHeaps (writer ctx) r s h h' |> Defined r
        | Merged ghs, _ ->
            let gs, hs = List.unzip ghs
            hs |> List.map (fun h -> composeGeneralizedHeaps writer ctx getter setter (setter s h) h') |> Merging.mergeGeneralizedHeaps gs
        | _, Merged ghs' ->
            let gs, hs' = List.unzip ghs'
            let gs' = List.map (fillHoles ctx s) gs
            hs' |> List.map (composeGeneralizedHeaps writer ctx getter setter s) |> Merging.mergeGeneralizedHeaps gs'
        | Defined _, Composition(s', ctx', h')
        | Mutation _, Composition(s', ctx', h')
        | Composition _, Composition(s', ctx', h') ->
            let s = composeStates ctx s s'
            composeGeneralizedHeaps writer ctx' getter setter s h'
        | Defined _, Mutation(h', h'')
        | RecursiveApplication _, Mutation(h', h'') //TODO: mb deleted
        | HigherOrderApplication _, Mutation(h', h'')
        | Composition _, Mutation(h', h'')
        | Mutation _, Mutation(h', h'') ->
            let res = composeGeneralizedHeaps writer ctx getter setter s h'
            let res' = fillHolesInHeap ctx s h''
            Mutation(res, res')
        | Defined _, HigherOrderApplication _
        | Defined _, RecursiveApplication _
        | Composition _, HigherOrderApplication _
        | Composition _, RecursiveApplication _
        | RecursiveApplication _, RecursiveApplication _
        | HigherOrderApplication _, HigherOrderApplication _ ->
            Composition(s, ctx, h')
        | Composition(s', ctx', h') as h, Defined(r'', h'') ->
            assert(not r'')
            match h' with
            | Defined(r, h') ->
                let ctx'' = decomposeContexts ctx ctx'
                let h = composeDefinedHeaps (writer ctx'') r s h' h'' |> Defined r
                composeGeneralizedHeaps writer ctx' getter setter s' h
            | _ ->
                let h'' = fillHolesInHeap ctx s h''
                Mutation(h, h'')
        | (HigherOrderApplication _ as h), Defined(r, h') //TODO: mb deleted
        | (RecursiveApplication _ as h), Defined(r, h') ->
            assert(not r)
            let h' = fillHolesInHeap ctx s h'
            Mutation(h, h')
        | Mutation(h, h'), Defined(r, h'') ->
            // TODO: this is probably wrong!
            assert(not r)
            Mutation(h, composeDefinedHeaps (writer ctx) false s h' h'')
        | RecursiveApplication _, Composition _ -> __notImplemented__()
        | HigherOrderApplication _, Composition _ -> __notImplemented__()
        | RecursiveApplication _, HigherOrderApplication _ -> __notImplemented__()
        | HigherOrderApplication _, RecursiveApplication _ -> __notImplemented__()
        | Mutation _, RecursiveApplication _ -> __notImplemented__()
        | Mutation _, HigherOrderApplication _ -> __notImplemented__()

    and composeStacksOf ctx state state' =
        (foldStackLocations (fillAndMutateStack ctx state) state state'.stack).stack

    and composeHeapsOf ctx state heap =
        composeGeneralizedHeaps fillAndMutateHeap ctx heapOf withHeap state heap

    and composeStaticsOf ctx state statics =
        composeGeneralizedHeaps fillAndMutateStatics ctx staticsOf withStatics state statics

    and composeStates ctx state state' =
        let stack = composeStacksOf ctx state state'
        let heap = composeHeapsOf ctx state state'.heap
        let statics = composeStaticsOf ctx state state'.statics
//        assert(state'.typeVariables |> snd |> Stack.isEmpty)
        let pc = List.map (fillHoles ctx state) state'.pc |> List.append state.pc
        { stack = stack; heap = heap; statics = statics; frames = state.frames; pc = pc; typeVariables = state.typeVariables }

// ------------------------------- High-level read/write -------------------------------

    and deref metadata state location =
        hierarchicalAccess true true npeTerm makePair metadata state location

    and derefWith actionNull metadata state location = hierarchicalAccess true true actionNull makePair metadata state location

    and derefWithoutValidation metadata state location =
        hierarchicalAccess false true (fun _ _ _ -> __unreachable__()) makePair metadata state location

    and mutate metadata state reference value =
        assert(value <> Nop)
        let time = tick()
        hierarchicalAccess true false npeTerm (fun _ _ -> (value, time)) metadata state reference

// ------------------------------- Referencing -------------------------------

    and private referenceTerm state name followHeapRefs term =
        match term.term with
        | Error _
        | PointerTo _ -> StackRef term.metadata name []
        | StackRef _
        | StaticRef _
        | HeapRef _ when followHeapRefs -> term
        | Union gvs -> Merging.guardedMap (referenceTerm state name followHeapRefs) gvs
        | _ -> StackRef term.metadata name []

    and referenceLocalVariable metadata state location followHeapRefs =
        let reference = StackRef metadata location []
        let term, state = deref metadata state reference
        referenceTerm state location followHeapRefs term

    let rec private referenceFieldOf state field parentRef reference =
        match reference with
        | ErrorT _ -> reference, state
        | { term = HeapRef((addr, path), t, ArrayContents, Reference _) } ->
            assert(List.isEmpty path)
            HeapRef reference.metadata (addr, [field]) ArrayContents t (snd field) , state
        | Null ->
            let term, state = State.createInstance reference.metadata typeof<System.NullReferenceException> [] state
            Error reference.metadata term, state
        | { term = Struct _ } -> referenceSubLocation field ArrayContents parentRef, state
        | UnionT gvs -> Merging.guardedStateMap (fun state term -> referenceFieldOf state field parentRef term) gvs state
        | t -> internalfailf "expected reference or struct, but got %O" t, state

    let rec private followOrReturnReference metadata state reference =
        let term, state = deref metadata state reference
        match term.term with
        | Error _
        | StackRef _
        | StaticRef _
        | IndentedPtr _
        | HeapRef _ -> term, state
        | Union gvs when List.forall (fun (_, t) -> isError t || isRef t) gvs ->
            Merging.guardedStateMap (followOrReturnReference metadata) gvs state
        | _ -> reference, state

    let referenceField metadata state followHeapRefs name typ parentRef =
        let typ = Types.wrapReferenceType typ
        let term, state = deref metadata state parentRef
        let reference, newState = referenceFieldOf state (makeStringKey name, typ) parentRef term
        if followHeapRefs then followOrReturnReference metadata newState reference
        else (reference, newState)

    let referenceStaticField metadata state followHeapRefs fieldName fieldType typeName =
        let fieldType = Types.wrapReferenceType fieldType
        let reference = StaticRef metadata typeName [(Terms.makeStringKey fieldName, fieldType)]
        if followHeapRefs then followOrReturnReference metadata state reference
        else (reference, state)

    let private checkIndices mtd state arrayRef (indices : term list) k =
        let intToTerm i = makeNumber i mtd
        let idOfDimensionsForLowerBounds = Seq.init indices.Length (intToTerm >> referenceArrayLowerBound arrayRef)
        let idOfDimensionsForLengths = Seq.init indices.Length (intToTerm >> referenceArrayLength arrayRef)
        Cps.Seq.mapFold (deref mtd) state idOfDimensionsForLowerBounds (fun (lowerBoundsList, state') ->
        Cps.Seq.mapFold (deref mtd) state' idOfDimensionsForLengths (fun (lengthsList, state'') ->
        let bounds =
            Seq.map3
                (fun idx low len ->
                    let up = add mtd low len
                    Arithmetics.simplifyGreaterOrEqual mtd idx low (fun bigEnough ->
                    Arithmetics.simplifyLess mtd idx up (fun smallEnough ->
                    bigEnough &&& smallEnough)))
                indices lowerBoundsList lengthsList
            |> List.ofSeq
        k (conjunction mtd bounds |> Merging.unguard |> Merging.merge , state'')))

    let referenceArrayIndex metadata state arrayRef (indices : term list) =
        let array, state = deref metadata state arrayRef
        // TODO: what about followHeapRefs?
        let rec reference state term =
            match term.term with
            | Error _ -> (term, state)
            | Array(_, _, _, _, _, _, ArrayType(elementType, _)) ->
                Common.statedConditionalExecution state
                    (fun state k -> checkIndices metadata state arrayRef indices k)
                    (fun state k ->
                        let location = Arrays.makeIntegerArray metadata (fun i -> indices.[i]) indices.Length
                        let result = referenceSubLocation (location, elementType) ArrayContents arrayRef
                        k (result, state))
                    (fun state k ->
                        let exn, state = State.createInstance metadata typeof<System.IndexOutOfRangeException> [] state
                        k (Error metadata exn, state))
                    Merging.merge Merging.merge2Terms id id
            | Union gvs -> Merging.guardedStateMap reference gvs state
            | t -> internalfailf "accessing index of non-array term %O" t
        reference state array

// ------------------------------- Allocation -------------------------------

    let newStackFrame state metadata funcId frame = State.newStackFrame (tick()) metadata state funcId frame
    let newScope metadata state frame = State.newScope (tick()) metadata state frame

    let freshHeapLocation metadata =
        Concrete metadata ([freshAddress()]) pointerType

    let allocateOnStack metadata s key term =
        let time = tick()
        let { func = frameMetadata; entries = oldFrame; time = frameTime } = Stack.peek s.frames.f
        let newStack = pushToCurrentStackFrame s key { value = term; created = time; modified = time }
        let newEntries = { key = key; mtd = metadata; typ = typeOf term }
        let stackFrames = Stack.updateHead s.frames.f { func = frameMetadata; entries = newEntries :: oldFrame; time = frameTime }
        { s with stack = newStack; frames = { s.frames with f = stackFrames } }

    let private allocateInDefinedHeap (h : symbolicHeap) address term time =
        h.Add(address, {value = term; created = time; modified = time })

    let rec private allocateInGeneralizedHeap address term time = function
        | Defined(r, h) -> allocateInDefinedHeap h address term time |> Defined r
        | Composition _
        | RecursiveApplication _
        | HigherOrderApplication _ as h ->
            let mutatedHeap = allocateInDefinedHeap Heap.empty address term time
            Mutation(h, mutatedHeap)
        | Mutation(gh, h) -> Mutation(gh, allocateInDefinedHeap h address term time)
        | Merged gvh ->
            Merging.commonGuardedMapk (fun h k -> k <| allocateInGeneralizedHeap address term time h) gvh
                (fun gvh ->
                    let g, h = List.unzip gvh
                    Merging.mergeGeneralizedHeaps g h) id

    let allocateInHeap metadata s term : term * state =
        let address = freshHeapLocation metadata
        let time = tick()
        let typ = typeOf term
        let pointer = HeapRef metadata ((address, typ), []) ArrayContents {v=time} typ
        (pointer, { s with heap = allocateInGeneralizedHeap address term time s.heap } )

    let allocateInStaticMemory metadata (s : state) typeName term =
        let time = tick()
        let address = makeConcreteString typeName metadata
        { s with statics = allocateInGeneralizedHeap address term time s.statics }

    let makeSymbolicThis metadata state token typ =
        let isRef = isReferenceType typ
        let thisKey = ((if isRef then "this" else Pointers.symbolicThisStackKey), token)
        let thisStackRef = StackRef metadata thisKey []
        let source = {location = thisStackRef; heap = None; extractor = IdTermExtractor()}
        let instance = makeSymbolicInstance metadata Timestamp.zero source "this" (wrapReferenceType typ)
        if isRef
            then instance, state, false
            else
                let key = (Pointers.symbolicThisStackKey, token)
                let state = newStackFrame state metadata (EmptyIdentifier()) [(key, Specified instance, typ)]
                referenceLocalVariable metadata state key true, state, true

// ------------------------------- Static Memory Initialization -------------------------------

    [<StructuralEquality;NoComparison>]
    type private staticsInitializedSource =
        {heap : generalizedHeap; key : term}
        interface IStatedSymbolicConstantSource with
            override x.SubTerms = Seq.singleton x.key

    let (|StaticsInitializedSource|_|) (src : ISymbolicConstantSource) =
        match src with
        | :? staticsInitializedSource as li -> Some(li.heap, li.key)
        | _ -> None

    let mutable counter = 0
    let private mkStaticKeyGuard mtd heap key =
        Constant mtd (IdGenerator.startingWith "hasKey#") ({heap = heap; key = key} : staticsInitializedSource) Bool

    let private staticGuardOfDefinedHeap mtd key r (h : symbolicHeap) =
            if h.ContainsKey key then Merging.guardOf h.[key].value
            elif r then False
            else mkStaticKeyGuard mtd (Defined r h) key

    let rec private staticGuardOfHeap (exploredRecursiveIds : ImmutableHashSet<IFunctionIdentifier>) mtd key = function
        | Defined(r, h) -> staticGuardOfDefinedHeap mtd key r h
        | Merged ghs -> Merging.guardedMap (staticGuardOfHeap exploredRecursiveIds mtd key) ghs
        | Mutation(h, h') ->
            staticGuardOfHeap exploredRecursiveIds mtd key h ||| staticGuardOfDefinedHeap mtd key false h'
        | Composition(s, ctx, h) ->
            staticGuardOfHeap exploredRecursiveIds mtd key s.statics ||| staticGuardOfHeap exploredRecursiveIds mtd (fillHoles ctx s key) h
        | RecursiveApplication(f, _, _) when exploredRecursiveIds.Contains f -> False
        | RecursiveApplication(f, _, _) ->
            match Database.querySummary f with
            | Some summary ->
                staticGuardOfHeap (exploredRecursiveIds.Add f) mtd key summary.state.statics
            | None -> True
        | HigherOrderApplication _ as h ->
            mkStaticKeyGuard mtd h key

    let private staticKeyInitialized mtd key state =
        staticGuardOfHeap ImmutableHashSet<IFunctionIdentifier>.Empty mtd key state.statics

    let internal typeNameInitialized mtd typeName state =
        staticKeyInitialized mtd (makeStringKey typeName) state

// ------------------------------- Compositions of constants -------------------------------

    type lazyInstantiation with
        interface IExtractingSymbolicConstantSource with
            override x.Compose ctx state =
                let state' =
                    match x.heap with
                    | Some heap ->
                        // TODO: make it more effective (use lower-level functions to access heap directly instead of creating fresh state)
                        match x.location.term with
                        | HeapRef _ -> { State.empty with heap = composeHeapsOf ctx state heap }
                        | StaticRef _ -> { State.empty with statics = composeStaticsOf ctx state heap }
                        | _ -> __notImplemented__()
                    | None -> state
                let loc = fillHoles ctx state x.location
                derefWithoutValidation ctx.mtd state' loc |> fst |> x.extractor.Extract

    type staticsInitializedSource with
        interface IStatedSymbolicConstantSource with
            override x.Compose ctx state =
                staticKeyInitialized ctx.mtd x.key state
