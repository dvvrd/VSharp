namespace VSharp.Core
open Types

#nowarn "69"

open VSharp
open VSharp.Core.Types.Constructor
open System.Collections.Immutable
open VSharp.Utils

module internal Memory =
    open Terms
    open Merging
    open State

// ------------------------------- Primitives -------------------------------

    let private pointer = persistent<int>(always 0, id)
    let freshAddress() =
        pointer.Mutate(pointer.Value + 1)
        pointer.Value
    let reset() =
        pointer.Reset()
    let saveConfiguration() =
        pointer.Save()
    let restore() =
        pointer.Restore()

    let npe mtd state = State.createInstance mtd typeof<System.NullReferenceException> [] state

    let private npeTerm mtd state _ =
        let exn, state = npe mtd state
        Error mtd exn, state

    let private referenceSubLocations term locations =
        let addLocationsToPath ref =
            match ref.term with
            | Ref(tl, path) -> Ref ref.metadata tl (List.append path locations)
            | Ptr(tl, path, typ, shift) -> AnyPtr ref.metadata tl (List.append path locations) typ shift
            | _ -> internalfailf "expected reference, but got %O" ref
        guardedErroredApply addLocationsToPath term

    let referenceArrayLowerBound arrayRef (indices : term) =
        referenceSubLocations arrayRef [ArrayLowerBound indices]

    let referenceArrayLength arrayRef (indices : term) =
        referenceSubLocations arrayRef [ArrayLength indices]

    let referenceBlockField structRef (field : fieldId) typ =
        referenceSubLocations structRef [BlockField(field, typ)]

// ------------------------------- Instantiation (lazy & default) -------------------------------

    [<StructuralEquality;NoComparison>]
    type private lazyInstantiation<'a when 'a : equality> =
        {location : term; heap : 'a generalizedHeap option; extractor : TermExtractor; typeExtractor : TypeExtractor}
        interface IExtractingSymbolicConstantSource with
            override x.SubTerms = Seq.singleton x.location
            override x.WithExtractor e = {x with extractor = e} :> IExtractingSymbolicConstantSource
        interface IExtractingSymbolicTypeSource with
            override x.WithTypeExtractor e = {x with typeExtractor = e} :> IExtractingSymbolicTypeSource
            override x.TypeCompose ctx state =
                (x :> IStatedSymbolicConstantSource).Compose ctx state |> typeOf |> x.typeExtractor.TypeExtract
            override x.TypeEquals other =
                match other with
                | :? lazyInstantiation<'a> as li -> x.location = li.location
                | _ -> false

    let lazyInstantiationWithExtractor location heap extractor typeExtractor : IExtractingSymbolicConstantSource =
        let gli heap = {location = location; heap = heap; extractor = extractor; typeExtractor = typeExtractor} :> IExtractingSymbolicConstantSource
        match heap, location.term with
        | None, Ref(RefTopLevelHeap _, _) -> gli (None : term generalizedHeap option)
        | None, Ref(RefTopLevelStatics _, _) -> gli (None : termType generalizedHeap option)
        | None, Ref(RefTopLevelStack _, _) -> gli (None : obj generalizedHeap option)
        | Some _, _ -> gli heap
        | _ -> __notImplemented__()

    let lazyInstantiation location heap = lazyInstantiationWithExtractor location heap (IdTermExtractor()) (IdTypeExtractor())

    type lazyInstantiation<'a when 'a : equality> with
        member x.WithLocation loc = lazyInstantiationWithExtractor loc x.heap x.extractor x.typeExtractor

    let (|LazyInstantiation|_|) (src : ISymbolicConstantSource) =
        match src with
        | :? lazyInstantiation<_> as li -> Some(li.location, li.heap, li.extractor :? IdTermExtractor)
        | _ -> None

    let internal bypassFields metadata isStatic f heap fql typ =
        let dotNetType = toDotNetType typ
        let fields = Reflection.fieldsOf isStatic dotNetType
        let addField heap (field, typ) =
            let termType = typ |> fromDotNetType
            let fql' = BlockField(field, termType) |> addToOptionFQL fql
            f heap metadata field termType fql'
        FSharp.Collections.Array.fold addField heap fields

    let private mkFields metadata isStatic mkField fql typ =
        let f heap metadata  name termType fql' =
            let value = mkField metadata name termType fql'
            let key = makeKey name fql' termType
            Heap.add key value heap
        bypassFields metadata isStatic f Heap.empty fql typ

    let internal mkFieldsForUnmarshaling metadata state mkField fql typ =
        let f (heap, state) metadata name termType fql' =
            let value, state = mkField metadata state name termType fql'
            let key = makeKey name fql' termType
            Heap.add key value heap, state
        bypassFields metadata false f (Heap.empty, state) fql typ

    let private mkStruct metadata isStatic mkField typ fql =
        let contents = mkFields metadata isStatic mkField fql typ
        Struct metadata contents typ

    let private mkClass metadata isStatic mkField typ fql =
        let contents = mkFields metadata isStatic mkField fql typ
        Class metadata contents

    let private mkBlock metadata isStatic mkField typ fql =
        Common.statelessConditionalExecutionWithMerge []
            (fun k -> k <| Common.isValueType metadata typ)
            (fun k -> k <| mkStruct metadata isStatic mkField typ fql)
            (fun k -> k <| mkClass metadata isStatic mkField typ fql)

    let rec defaultOf metadata typ fql =
        match typ with
        | Bool -> makeFalse metadata
        | Numeric(Id t) -> CastConcrete true 0 t metadata
        | ArrayType _
        | ClassType _
        | InterfaceType _ -> makeNullRef metadata
        | TypeVariable (Id t) ->
            Common.statelessConditionalExecutionWithMerge []
                (fun k -> k <| Common.isValueType metadata typ)
                (fun k -> k <| CastConcrete false 0 t metadata) // TODO: add "default" symbolic constant source
                (fun k -> k <| makeNullRef metadata)
        | StructType _ ->
            mkStruct metadata false (fun m _ t -> defaultOf m t) typ fql
        | Pointer typ -> makeNullPtr metadata typ
        | _ -> __notImplemented__()

    let mkDefaultBlock metadata targetType fql =
        mkBlock metadata false (fun m _ t -> defaultOf m t) targetType fql

    let private makeSymbolicHeapReference metadata (source : IExtractingSymbolicConstantSource) name typ construct =
        let source' = source.WithExtractor(Pointers.HeapAddressExtractor())
        let constant = Constant metadata name source' pointerType
        construct metadata constant typ typ []

    let private makeSymbolicOveralArrayLength metadata (source : IExtractingSymbolicConstantSource) arrayName =
        Constant metadata (sprintf "|%s|" arrayName) (source.WithExtractor(Arrays.LengthExtractor())) lengthType

    let private makeSymbolicArrayRank metadata (source : IExtractingSymbolicConstantSource) arrayName =
        Constant metadata ("RankOf_%s" + arrayName) (source.WithExtractor(Arrays.RankExtractor())) lengthType

    let private makeSymbolicArrayLowerBound metadata name fql heap =
        match Options.ExplorationMode() with
        | TrustConventions -> defaultOf metadata lengthType <| Some fql
        | CompleteExploration ->
            let liSource = lazyInstantiation (makeFQLRef metadata fql) heap
            Constant metadata name liSource lengthType

    let private makeSymbolicArrayLength metadata name fql heap =
        let liSource = lazyInstantiation (makeFQLRef metadata fql) heap
        Constant metadata name liSource lengthType

    let private makeSymbolicArrayLowerBounds metadata (source : IExtractingSymbolicConstantSource) arrayName dimension fql =
        match source with
        | :? lazyInstantiation<term> as liSource ->
            match Options.ExplorationMode() with
            | TrustConventions -> Arrays.zeroLowerBounds metadata dimension fql
            | CompleteExploration ->
                let idOfBound i = sprintf "%s.%i_LowerBound" arrayName i
                let mkLowerBound i =
                    let liSourceI = liSource.WithLocation(referenceArrayLowerBound liSource.location (makeNumber metadata i))
                    Constant metadata (idOfBound i) liSourceI lengthType
                Seq.foldi (fun h i l -> Heap.add (makePathIndexKey metadata ArrayLowerBound i fql lengthType) l h) Heap.empty (Seq.init dimension mkLowerBound)
        | _ -> __notImplemented__()

    let private makeSymbolicArrayLengths metadata (source : IExtractingSymbolicConstantSource) arrayName dimension fql =
        match source with
        | :? lazyInstantiation<term> as liSource ->
            let idOfLength i = sprintf "%s.%i_Length" arrayName i
            let mkLength i =
                let liSourceI = liSource.WithLocation(referenceArrayLength liSource.location (makeNumber metadata i))
                Constant metadata (idOfLength i) liSourceI lengthType
            let lengths = Seq.init dimension mkLength
            let length = Seq.reduce (mul metadata) lengths
            Seq.foldi (fun h i l -> Heap.add (makePathIndexKey metadata ArrayLength i fql lengthType) l h) Heap.empty lengths, length
        | _ -> __notImplemented__()

    let private makeSymbolicArray metadata source dimension elemTyp arrayName fql =
        let instantiator = [True, LazyInstantiator elemTyp]
        let lowerBound, arrayLengths, arrayLength, dim =
            let makeConcrete d =
                let lb = makeSymbolicArrayLowerBounds metadata source arrayName d fql
                let al, length = makeSymbolicArrayLengths metadata source arrayName d fql
                lb, al, length, makeNumber metadata d
            match dimension with
            | Vector -> makeConcrete 1
            | ConcreteDimension d -> makeConcrete d
            | SymbolicDimension ->
                let length = makeSymbolicOveralArrayLength metadata source arrayName
                Heap.empty, Heap.empty, length, makeSymbolicArrayRank metadata source arrayName
        Array metadata dim arrayLength lowerBound instantiator Heap.empty arrayLengths

    let private makeSymbStrArray metadata strLength arrayFQL _ _ =
        let instantiator = [True, LazyInstantiator Char]
        Strings.makeStringArray metadata strLength instantiator Heap.empty arrayFQL

    let private makeSymbolicString mtd (source : IExtractingSymbolicConstantSource) strName fql =
        match source with
        | :? lazyInstantiation<term> as liSource ->
            let makeSymbolicStringField key t makeField =
                let ref = referenceBlockField liSource.location key t
                makeField (liSource.WithLocation(ref)) t
            let lengthName = sprintf "%s.m_StringLength" strName
            let length = makeSymbolicStringField Strings.strLength lengthType (Constant mtd lengthName)
            let arrayFQL = Strings.makeArrayFQL fql
            let array = makeSymbolicStringField Strings.strArray (ArrayType (Char, Vector)) (makeSymbStrArray mtd length arrayFQL)
            Strings.makeStringOfFields mtd length array arrayFQL fql
        | _ -> __notImplemented__()

    let private makeSymbolicReferenceType metadata blockBuilder source name typ = function
        | Some(HeapTopLevelHeap _, [])
        | Some(HeapTopLevelStatics _, []) -> blockBuilder ()
        | _ -> makeSymbolicHeapReference metadata source name typ HeapRef

    let private makeSymbolicClass metadata source name typ fql =
        let makeClass () = Class metadata Heap.empty
        makeSymbolicReferenceType metadata makeClass source name typ fql

    let rec makeSymbolicInstance metadata source name typ fql =
        match typ with
        | Bool
        | Numeric _ -> Constant metadata name source typ
        | StructType _ -> makeSymbolicStruct metadata source name typ fql
        | TypeVariable _ ->
            Common.statelessConditionalExecutionWithMerge []
                (fun k -> k <| Common.isValueType metadata typ)
                (fun k -> k <| Constant metadata name source typ)
                (fun k -> k <| makeSymbolicClass metadata source name typ fql)
        | StringType ->
            let makeString () = makeSymbolicString metadata source name fql
            makeSymbolicReferenceType metadata makeString source name typ fql
        | ClassType _ -> makeSymbolicClass metadata source name typ fql
        | InterfaceType _ -> makeSymbolicHeapReference metadata source name typ HeapRef // makes reference, because we will never have interface instance in heap
        | ArrayType(e, d) ->
            let makeArray () = makeSymbolicArray metadata source d e name fql
            makeSymbolicReferenceType metadata makeArray source name typ fql
        | Pointer typ' ->
            let makePtr mtd tl bTyp sTyp path = HeapPtr mtd tl bTyp sTyp path sTyp
            makeSymbolicHeapReference metadata source name typ' makePtr
        | Null -> makeNullRef metadata
        | Void -> Nop
        | Bottom -> __unreachable__()

    and private makeSymbolicStruct metadata (source : IExtractingSymbolicConstantSource) structName typ fql =
        let makeSymbolicStruct' (liSource : 'a lazyInstantiation) =
            let makeField mtd name typ fql =
                let fieldName = sprintf "%s.%O" structName name
                let fieldSource = liSource.WithLocation(referenceBlockField liSource.location name typ)
                makeSymbolicInstance mtd fieldSource fieldName typ fql
            mkStruct metadata false makeField typ fql
        match source with
        | :? lazyInstantiation<obj> as liSource -> makeSymbolicStruct' liSource
        | :? lazyInstantiation<term> as liSource -> makeSymbolicStruct' liSource
        | :? lazyInstantiation<termType> as liSource -> makeSymbolicStruct' liSource
        | _ -> __notImplemented__()

    let private genericLazyInstantiator metadata heap fql typ () =
        let source = lazyInstantiation (makeFQLRef metadata fql) heap
        makeSymbolicInstance metadata source (nameOfLocation fql) typ (Some fql)

    let () =
        State.genericLazyInstantiator <- fun mtd -> genericLazyInstantiator mtd None

    let private arrayElementLazyInstantiator metadata instantiator typ heap fql idx = function
        | DefaultInstantiator concreteType -> fun () -> defaultOf metadata (typ |?? concreteType) <| Some fql
        | LazyInstantiator concreteType -> instantiator |?? fun () ->
            let id = sprintf "%s[%s]" (nameOfLocation fql) (idx.term.IndicesToString())
            let source = lazyInstantiation (makeFQLRef metadata fql) heap
            makeSymbolicInstance metadata source id concreteType (Some fql)
    let private arrayLowerBoundLazyInstantiator metadata instantiator _ heap fql (idx : term) = function
        | DefaultInstantiator _-> fun () -> defaultOf metadata lengthType <| Some fql
        | LazyInstantiator _ -> instantiator |?? fun () ->
            let name = sprintf "%O.%s_LowerBound" (nameOfLocation fql) (idx.term.IndicesToString())
            makeSymbolicArrayLowerBound metadata name fql heap

    let private arrayLengthLazyInstantiator metadata instantiator _ heap fql (idx : term) = function
        | DefaultInstantiator _ -> fun () ->
            // In case when array was allocated during the interpretation (and thus has default instantiator) lengths by
            // all dimensions are known (they can be symbolic, but still defined). If this code triggers then we have
            // requested length by a greater dimension than our array has. That can happen in case of comparison of array
            // lengths when arrays have different ranks. In that case we consider lengths in all other dimensions equal to 1.
            makeNumber metadata 1
        | LazyInstantiator _ -> instantiator |?? fun () ->
            let name = sprintf "%O.%s_Length" (nameOfLocation fql) (idx.term.IndicesToString())
            makeSymbolicArrayLength metadata name fql heap

    let staticMemoryLazyInstantiator metadata typ () =
        match typ with
        | ReferenceType -> Class metadata Heap.empty
        | StructureType -> Struct metadata Heap.empty typ
        | _ -> __unreachable__()

    let private selectLazyInstantiator metadata heap fql typ =
        match fql with
        | _, (_::_ as path) when isArrayLengthSeg <| List.last path -> fun () -> makeSymbolicArrayLength metadata (nameOfLocation fql + "_Length") fql heap
        | _, (_::_ as path) when isArrayLowerBoundSeg <| List.last path -> fun () -> makeSymbolicArrayLowerBound metadata (nameOfLocation fql + "_LowerBound") fql heap
        | HeapTopLevelStatics _, [] -> staticMemoryLazyInstantiator metadata typ
        | _ -> genericLazyInstantiator metadata heap fql typ

// ------------------------------- Locations comparison -------------------------------

    type private 'key pointerInfo = { location : 'key; fullyQualifiedLocation : heapFQL; typ : termType; path : pathSegment list }

    let private canPoint mtd keyCompare ptr key = // TODO: implement using fql compare
        // TODO: what if locationType is Null?
        let addrEqual = keyCompare mtd ptr.location key.key
        let typeEqual = Common.typesEqual mtd ptr.typ key.typ
        if isConcrete addrEqual then addrEqual else addrEqual &&& typeEqual

    let private findSuitableLocations<'key when 'key : equality> mtd h keyCompare contextList mapper (ptr : 'key pointerInfo) =
        let filterMapKey (key : 'key memoryCell, v) =
            let k, v = List.fold mapper (key.key, v) contextList // TODO: fillHoles in fql
            let key = {key with key = k}
            let guard = canPoint mtd keyCompare ptr key
            match guard with
            | False -> None
            | _ -> Some(guard, key, v)
        let gvs = h |> Heap.toSeq |> List.ofSeq |> List.choose filterMapKey
        let baseGvs, restGvs = gvs |> List.partition (fst3 >> isTrue)
        let baseGvs = List.map (fun (_, k, v) -> k, v) baseGvs
        assert(List.length baseGvs <= 1)
        List.tryHead baseGvs, restGvs

// ------------------------------- Primitive read/write -------------------------------

    let private stackDeref instantiateLazy state location =
        if isAllocatedOnStack state location then
            (readStackLocation state location, state)
        else
            let lazyInstance = instantiateLazy()
            (lazyInstance, writeStackLocation state location lazyInstance)

    let private writeHeap guard h key newValue =
        assert(Heap.contains key h)
        let oldValue = Heap.find key h
        let value = merge2Terms guard !!guard newValue oldValue
        Heap.add key value h

// ------------------------------- Core -------------------------------

    let rec private accessHeap<'a, 'key when 'a : equality and 'key : equality> read restricted metadata (groundHeap : 'a generalizedHeap option) guard update (h : 'key heap) keyCompare contextList mapper lazyInstantiator ptr =
        let accessRec gvas lazyValue h =
            let accessLocation h (guard', key, value) =
                let guard'' = guard &&& guard'
                let reversedFql = getFQLOfKey key |> reverseFQL
                let accessedValue, newBaseValue = accessTerm read metadata groundHeap guard'' update contextList lazyInstantiator reversedFql ptr.path value
                let h' = if read || value = newBaseValue then h else writeHeap guard'' h key newBaseValue
                assert(key.typ = baseTypeOfKey key)
                (guard'', accessedValue), h'
            let gvs, h' = List.mapFold accessLocation h gvas
            merge (optCons gvs lazyValue), h'
        let heapKey = makeKey ptr.location (Some ptr.fullyQualifiedLocation) ptr.typ
        if Heap.contains heapKey h then // TODO: only if heapKey is concreteHeapAddress!
            accessRec [(makeTrue metadata, heapKey, Heap.find heapKey h)] None h
        else
            let baseGav, restGavs = findSuitableLocations metadata h keyCompare contextList mapper ptr
            match baseGav with
            | None when read && restricted ->
                // TODO: undefined behaviour detected!
                __notImplemented__()
            | None ->
                let baseGuard = restGavs |> List.map (fst3 >> (!!)) |> conjunction metadata
                let lazyValue =
                    if read && isTopLevelHeapConcreteAddr ptr.fullyQualifiedLocation && List.isEmpty contextList && List.isEmpty ptr.path
                        then Union metadata [] // TODO: incorrect deref during independent check (Test -- RecursiveAccess.G)
                        else lazyInstantiator |?? genericLazyInstantiator metadata groundHeap ptr.fullyQualifiedLocation ptr.typ |> eval
                let gavs = if read then restGavs else (baseGuard, heapKey, lazyValue)::restGavs
                let lv = if read then Some(baseGuard, lazyValue) else None
                let h = if read then h else Heap.add heapKey lazyValue h
                accessRec gavs lv h
            | Some(k, v) -> accessRec ((makeTrue metadata, k, v)::restGavs) None h

    and private accessTerm read metadata (groundHeap: 'a generalizedHeap option) guard (update : heapFQL * term -> term) contextList lazyInstantiator (ptrFql : heapFQL) path value =
        let internalMerge gvs =
            let cells, newVs = List.fold (fun (cells, newVs) (g, (c, v)) -> (g, c)::cells, (g, v)::newVs) ([], []) gvs
            merge cells, merge newVs
        let doAccess term =
            match path with
            | [] ->
                let newTerm = update (ptrFql, term)
                newTerm, newTerm
            | location :: path' ->
                match term.term with
                | Block(fields, blockType) ->
                    let fql' = addToFQL location ptrFql
                    match location with
                    | BlockField(name, typ) ->
                        let instantiator = if read then lazyInstantiator else Some <| genericLazyInstantiator term.metadata groundHeap fql' typ
                        let ptr' = { location = name; fullyQualifiedLocation = fql'; typ = typ; path = path' }
                        let mapper (k, term) (ctx, s) = k, fillHoles ctx s term
                        let resultCell, newFields = accessHeap<'a, fieldId> read false metadata groundHeap guard update fields compareStringKey contextList mapper instantiator ptr'
                        resultCell, Block term.metadata newFields blockType
                    | _ -> __unreachable__()
                | Array(dimension, length, lower, constant, contents, lengths) ->
                    let fql' = addToFQL location ptrFql
                    let newHeap heap instor keyCompare ptr = accessHeap<'a, term> read false metadata groundHeap guard update heap keyCompare contextList termKeyMapper (Some instor) ptr
                    let makePtr key typ = { location = key; fullyQualifiedLocation = fql'; typ = typ; path = path' }
                    let makeInstantiator key instantiator =
                        let realInstantiator, targetType = if read then lazyInstantiator, Some(typeOfPath path) else None, None
                        let doJob = lazy(guardedMap (fun c -> instantiator term.metadata realInstantiator targetType groundHeap fql' key c ()) constant)
                        doJob.Force
                    match location with
                    | ArrayIndex(key, typ) ->
                        let instantiator = makeInstantiator key arrayElementLazyInstantiator
                        let resultCell, newContents = newHeap contents instantiator Arrays.equalsArrayIndices <| makePtr key typ
                        resultCell, Array term.metadata dimension length lower constant newContents lengths
                    | ArrayLength key ->
                        let instantiator = makeInstantiator key arrayLengthLazyInstantiator
                        let resultCell, newLengths = newHeap lengths instantiator fastNumericCompare <| makePtr key lengthType
                        resultCell, Array term.metadata dimension length lower constant contents newLengths
                    | ArrayLowerBound key ->
                        let instantiator = makeInstantiator key arrayLowerBoundLazyInstantiator
                        let resultCell, newLower = newHeap lower instantiator fastNumericCompare <| makePtr key lengthType
                        resultCell, Array term.metadata dimension length newLower constant contents lengths
                    | _ -> __unreachable__()
                | t -> internalfailf "expected complex type, but got %O" t
        commonGuardedErroredApply doAccess (withFst value) value internalMerge

    and private compareStringKey mtd loc key = makeBool mtd (loc = key)

    and private readTerm mtd (_ : bool) term ((tl, path) as fql) typ =
        let currentPath, path' = List.splitAt (List.length path - 1) path
        let lazyInstor = genericLazyInstantiator mtd None fql typ
        accessTerm true mtd None (makeTrue mtd) snd [] (Some lazyInstor) (tl, currentPath) path' term |> fst

    and private accessBlockField read mtd update term fieldName fieldType =
        let lazyInstor = __unreachable__
        let path = [BlockField(fieldName, fieldType)]
        let fakeFql = (HeapNullAddress, []) // TODO: fix and never use fake fql
        accessTerm read mtd None (makeTrue mtd) update [] (Some lazyInstor) fakeFql path term |> fst

    and private commonHierarchicalStackAccess read update metadata state location path =
        let firstLocation = HeapTopLevelStack location, []
        let value, _ = stackDeref (stackLazyInstantiator state location) state location
        let termLazyInstantiator = if read && not (List.isEmpty path) then genericLazyInstantiator metadata None (HeapTopLevelStack location, path) (typeOfPath path) else __unreachable__
        let accessedValue, newBaseValue = accessTerm read metadata None (makeTrue metadata) update [] (Some termLazyInstantiator) firstLocation path value
        let newState = if read || value = newBaseValue then state else writeStackLocation state location newBaseValue
        accessedValue, newState

    and private termKeyMapper (k, v) (ctx, s) = fillHoles ctx s k, fillHoles ctx s v

    and private commonHierarchicalHeapAccess read restricted update metadata groundHeap heap contextList lazyInstantiator addr typ path = // TODO: use fql instead of typ and path
        let firstLocation = HeapTopLevelHeap(addr, typ), []
        let typ' = if List.isEmpty path then typ else typeOfPath path
        let readInstor = lazyInstantiator |?? selectLazyInstantiator metadata groundHeap (HeapTopLevelHeap(addr, typ), path) typ'
        let lazyInstantiator = if read then Some readInstor else None
        let ptr = {location = addr; fullyQualifiedLocation = firstLocation; typ = typ; path = path} // TODO: ptr takes only current fql and path
        accessHeap<term, term> read restricted metadata groundHeap (makeTrue metadata) update heap fastNumericCompare contextList termKeyMapper lazyInstantiator ptr

    and readHeap metadata restricted heap key typ =
        commonHierarchicalHeapAccess true restricted snd metadata None heap [] None key typ [] |> fst

    and private commonHierarchicalStaticsAccess read restricted update metadata groundHeap statics contextList lazyInstantiator typ path =
        let typ' = if List.isEmpty path then typ else typeOfPath path
        let lazyInstantiator =
            if read then
                let readInstor = lazyInstantiator |?? selectLazyInstantiator metadata groundHeap (HeapTopLevelStatics typ, path) typ'
                Some readInstor
            else None
        let ptr = {location = typ; fullyQualifiedLocation = HeapTopLevelStatics typ, []; typ = typ; path = path}
        let mapper (k, v) (ctx, s) = substituteTypeVariables ctx s k, fillHoles ctx s v
        accessHeap<termType, termType> read restricted metadata groundHeap (makeTrue metadata) update statics Common.typesEqual contextList mapper lazyInstantiator ptr

    and readStatics metadata restricted statics key _ =
        commonHierarchicalStaticsAccess true restricted snd metadata None statics [] None key [] |> fst

    and updateStack update metadata state location path =
        commonHierarchicalStackAccess false update metadata state location path |> snd

    and mutateStack metadata state location path value = updateStack (always value) metadata state location path

    and private updateHeap restricted update metadata h loc typ path =
        commonHierarchicalHeapAccess false restricted update metadata None h [] None loc typ path |> snd

    and private mutateHeap restricted metadata h loc typ path value = updateHeap restricted (always value) metadata h loc typ path

    and private updateStatics restricted update metadata statics location _ path =
        commonHierarchicalStaticsAccess false restricted update metadata None statics [] None location path |> snd

    and private mutateStatics restricted metadata statics location typ path value = updateStatics restricted (always value) metadata statics location typ path

    and private independent<'a when 'a : equality> (exploredRecursiveCodeLocs : ImmutableHashSet<ICodeLocation>) (read : ImmutableHashSet<ICodeLocation> -> state -> term * 'a generalizedHeap) codeLoc location : bool =
        exploredRecursiveCodeLocs.Contains codeLoc ||
        let exploredRecursiveIds = exploredRecursiveCodeLocs.Add codeLoc
        match Database.querySummary codeLoc with
        | Some summary ->
            let t, _ = read exploredRecursiveIds summary.state
            let li = genericLazyInstantiator Metadata.empty (None : 'a generalizedHeap option) (getFQLOfRef location) (typeOf location) ()
            li = t
        | None -> false

    and private accessGeneralizedHeapRec<'a when 'a : equality> (exploredIds : ImmutableHashSet<ICodeLocation>) unlucky contextList lazyInstantiator read readHeap (getter : state -> 'a generalizedHeap) location accessDefined = function
        | Defined(r, h) ->
            let result, heap = accessDefined contextList lazyInstantiator None r h
            result, Defined r heap
        | Merged ghs ->
            let foldFunc (g, h) (gvs, gs, hs) =
                let v, h' = accessGeneralizedHeapRec exploredIds unlucky contextList lazyInstantiator read readHeap getter location accessDefined h
                ((g, v)::gvs, g::gs, h'::hs)
            let gvs, gs, hs = List.foldBack foldFunc ghs ([], [], [])
            merge gvs, mergeGeneralizedHeaps readHeap gs hs
        | Mutation(h, h') as m ->
            let result, h'' = accessDefined contextList lazyInstantiator (Some h) false h'
            if read then
                let accessH = lazy(accessGeneralizedHeapRec exploredIds unlucky contextList lazyInstantiator read readHeap getter location accessDefined h |> fst)
                let simplifyInstantiated contextCase nonContextCase term =
                    match term.term with
                    | Constant(_, LazyInstantiation(loc, Some heap, _), _) when loc = location && heap = h ->
                        accessH.Force() |> contextCase
                    | _ -> nonContextCase term
                let simplifyInstantiatedAddress address baseType sightType =
                    simplifyInstantiated (topLevelOfFilledRef sightType) (fun a -> [True, RefTopLevelHeap(a, baseType, sightType)]) address
                Substitution.substitute (simplifyInstantiated id id) simplifyInstantiatedAddress id result, m
            else
                result, Mutation(h, h'')
        | Composition(_, _, Defined _) ->
            internalfail "composition with the defined heap should not be met, it must be simplified to a simple mutation!"
        | Composition(s, ctx, h) as heap when read ->
            let unlucky _ = unlucky heap  // if simplification of 'h' fails then we should return 'heap' instead of 'h'
            let lazyInstantiator' = lazy(accessGeneralizedHeapRec exploredIds unlucky contextList lazyInstantiator read readHeap getter location accessDefined (getter s) |> fst)
            accessGeneralizedHeapRec exploredIds unlucky ((ctx, s) :: contextList) (Some lazyInstantiator'.Force) read readHeap getter location accessDefined h
        | RecursiveApplication(codeLoc, _) as h
                when read && independent exploredIds
                                 (fun ids s -> accessGeneralizedHeapWithIDs ids read readHeap getter location accessDefined (getter s)) codeLoc location ->
            let r, _ = accessDefined contextList lazyInstantiator None false Heap.empty
            r, h
        | Composition _
        | RecursiveApplication _
        | HigherOrderApplication _ as h -> unlucky h contextList
        | _ -> __unreachable__()

    and private accessGeneralizedHeapWithIDs exploredIds (read : bool) readHeap getter location accessDefined =
        let unlucky h contextList =
            let r, e = accessDefined contextList None (Some h) false Heap.empty
            r, if read then h else Mutation(h, e)
        accessGeneralizedHeapRec<'a> exploredIds unlucky [] None read readHeap getter location accessDefined

    and private accessGeneralizedHeap read = accessGeneralizedHeapWithIDs ImmutableHashSet.Empty read

    and private hierarchicalAccess validate read actionNull updateDefined metadata =
        let doAccess state term = // TODO: track current heap address inside Ref (need for RecursiveAccess.MemoryTest)
            match term.term with
            | Ref(RefNullAddress, _) -> actionNull metadata state Null
            | Ref(RefTopLevelStack location, path) ->
                commonHierarchicalStackAccess read updateDefined metadata state location path
            | Ref(RefTopLevelHeap(addr, bT, _), path) ->
                let doRead state k =
                    let accessDefined contextList lazyInstantiator groundHeap r h =
                        commonHierarchicalHeapAccess read r updateDefined metadata groundHeap h contextList lazyInstantiator addr bT path
                    let result, h' = accessGeneralizedHeap read (readHeap metadata) heapOf term accessDefined (heapOf state)
                    k (result, withHeap state h')
                if validate then
                    Common.statedConditionalExecutionWithMerge state
                        (fun state k -> k (Pointers.isZeroAddress metadata addr, state))
                        (fun state k -> k (actionNull metadata state bT))
                        doRead
                else doRead state id
            | Ref(RefTopLevelStatics location, path) ->
                let accessDefined contextList lazyInstantiator groundHeap r h =
                    commonHierarchicalStaticsAccess read r updateDefined metadata groundHeap h contextList lazyInstantiator location path
                let result, m' = accessGeneralizedHeap read (readStatics metadata) staticsOf term accessDefined (staticsOf state)
                result, withStatics state m'
            | Ptr(_, _, viewType, shift) ->
                let ref = getReferenceFromPointer metadata term
                let term, state = hierarchicalAccess validate read actionNull updateDefined metadata state ref
                match shift with
                | None when typeOf term = viewType -> term, state
                | _ -> __notImplemented__() // TODO: [columpio] [Reinterpretation]
            | t -> internalfailf "expected reference or pointer, but got %O" t
        guardedErroredStatedApply doAccess

// ---------------------------------------------------- Composition ----------------------------------------------------

    and private fillHole (ctx : compositionContext) state term =
        match term.term with
        | Constant(_, source, _) ->
            match source with
            | :? IStatedSymbolicConstantSource as source -> source.Compose ctx state
            | :? INonComposableSymbolicConstantSource -> term
            | _ -> __notImplemented__()
        | Concrete(:? concreteHeapAddress as addr', t) ->
            Concrete ctx.mtd (composeAddresses ctx.addr addr') t
        | Concrete(:? concreteTypeAddress, _) -> term
        | Pointers.SymbolicThisOnStack(token, path) ->
            let id = ThisKey token
            let reference = referenceLocalVariable term.metadata id |> deref term.metadata state |> fst
            referenceSubLocations reference path
        | _ -> term

    and private topLevelOfFilledRef sightType reference =
        let destruct reference =
            match reference.term with
            | Ref(RefTopLevelHeap (a, bt, _), [])
            | Ptr(RefTopLevelHeap (a, bt, _), [], _, _) -> RefTopLevelHeap(a, bt, sightType)
            | Ref(RefNullAddress, [])
            | Ptr(RefNullAddress, [], _, _) -> RefNullAddress
            | _ -> __notImplemented__()
        unguard reference |> List.filter (fun (_, v) -> not <| isError v) |> guardedMapWithoutMerge destruct

    and private fillHoleInHeapAddress (ctx : compositionContext) state address baseType sightType = // TODO: find another solution someday..
        match address.term with
        | Constant(_, source, _) ->
            match source with
            | :? IExtractingSymbolicConstantSource as source ->
                let reference = source.ComposeWithoutExtractor ctx state
                topLevelOfFilledRef sightType reference
            | _ -> __notImplemented__()
        | Concrete(:? concreteHeapAddress as addr, t) ->
            let addr' = Concrete ctx.mtd (composeAddresses ctx.addr addr) t
            [True, RefTopLevelHeap(addr', baseType, sightType)]
        | Concrete(:? concreteTypeAddress, _) ->
            [True, RefTopLevelHeap(address, baseType, sightType)]
        | _ -> __notImplemented__()

    and fillHoles ctx state term =
        Substitution.substitute (fillHole ctx state) (fillHoleInHeapAddress ctx state) (substituteTypeVariables ctx state) term

    and private fillHolesInHeap keySubst ctx state heap =
        Substitution.substituteHeap (keySubst ctx state) (fillHole ctx state) (fillHoleInHeapAddress ctx state) (substituteTypeVariables ctx state) heap

    and private fillHolesInMemoryCell ctx keySubst state key =
        Substitution.substituteHeapKey (keySubst ctx state) (fillHole ctx state) (fillHoleInHeapAddress ctx state) (substituteTypeVariables ctx state) key

    and private updateLocation newValue (currentFQL, oldValue) = // TODO: support updating union with union
        let mtd = newValue.metadata
        let mutateOneKey old k v =
            let path = getFQLOfKey k |> snd |> List.last |> List.singleton
            accessTerm false mtd None True (updateLocation v) [] None currentFQL path old |> snd
        let doMutate newValue =
            match newValue.term with
            | Block(fields, _) ->
                Heap.fold mutateOneKey oldValue fields
            | Array(_, _, lower, _, contents, lengths) ->
                let oldValue = Heap.fold mutateOneKey oldValue lower
                let oldValue = Heap.fold mutateOneKey oldValue contents
                Heap.fold mutateOneKey oldValue lengths
            | _ -> newValue
        guardedErroredApply doMutate newValue

    and private fillAndMutateHeapLocation updateHeap keySubst ctx restricted state h k v =
        let k' = fillHolesInMemoryCell ctx keySubst state k
        let v' = fillHoles ctx state v
        let fql' = getFQLOfKey k'
        if (isTopLevelHeapConcreteAddr fql' || isTopLevelStatics fql') && not (Heap.contains k' h)
        then Heap.add k' v' h
        else updateHeap restricted (updateLocation v') ctx.mtd h k'.key k'.typ []

    and private fillAndMutateStackLocation (ctx : compositionContext) state memory k v =
        let v' = fillHoles ctx state v
        match k with
        | SymbolicThisKey token ->
            let loc = ThisKey token
            let thisRef = stackDeref (stackLazyInstantiator state loc) state loc |> fst
            update (updateLocation v') ctx.mtd memory thisRef |> snd
        | loc -> updateStack (updateLocation v') ctx.mtd memory loc []

    and private composeDefinedHeaps updateHeap keySubst (ctx : compositionContext) restricted state h h' =
        Heap.fold (fillAndMutateHeapLocation updateHeap keySubst ctx restricted state) h h'

    and private composeGeneralizedHeaps<'key when 'key : equality> readHeap updateHeap keySubst (ctx : compositionContext) getter setter s (h' : 'key generalizedHeap) : 'key generalizedHeap =
        match getter s, h' with
        | Defined(r, h), Defined(r', h') ->
            assert(not r')
            composeDefinedHeaps updateHeap keySubst ctx r s h h' |> Defined r
        | Merged ghs, _ ->
            let gs, hs = List.unzip ghs
            hs |> List.map (fun h -> composeGeneralizedHeaps readHeap updateHeap keySubst ctx getter setter (setter s h) h') |> mergeGeneralizedHeaps (readHeap ctx.mtd) gs
        | _, Merged ghs' ->
            let gs, hs' = List.unzip ghs'
            let gs' = List.map (fillHoles ctx s) gs
            hs' |> List.map (composeGeneralizedHeaps readHeap updateHeap keySubst ctx getter setter s) |> mergeGeneralizedHeaps (readHeap ctx.mtd) gs'
        | Defined _, Composition(s', ctx', h')
        | Mutation _, Composition(s', ctx', h')
        | Composition _, Composition(s', ctx', h') ->
            let s = composeStates ctx s s'
            composeGeneralizedHeaps readHeap updateHeap keySubst ctx' getter setter s h'
        | Defined _, Mutation(h', h'')
        | RecursiveApplication _, Mutation(h', h'')
        | HigherOrderApplication _, Mutation(h', h'')
        | Composition _, Mutation(h', h'')
        | Mutation _, Mutation(h', h'') ->
            let res = composeGeneralizedHeaps readHeap updateHeap keySubst ctx getter setter s h'
            let res' = fillHolesInHeap keySubst ctx s h''
            Mutation(res, res')
        | Defined _, HigherOrderApplication _
        | Defined _, RecursiveApplication _
        | Composition _, HigherOrderApplication _
        | Composition _, RecursiveApplication _
        | RecursiveApplication _, RecursiveApplication _
        | HigherOrderApplication _, HigherOrderApplication _
        | RecursiveApplication _, Composition _
        | HigherOrderApplication _, Composition _
        | RecursiveApplication _, HigherOrderApplication _
        | HigherOrderApplication _, RecursiveApplication _
        | Mutation _, RecursiveApplication _
        | Mutation _, HigherOrderApplication _  ->
            Composition(s, ctx, h')
        | Composition(s', ctx', h') as h, Defined(r'', h'') ->
            assert(not r'')
            match h' with
            | Defined(r, h') ->
                let h = composeDefinedHeaps updateHeap keySubst ctx' r s h' h'' |> Defined r
                composeGeneralizedHeaps readHeap updateHeap keySubst ctx getter setter s' h
            | _ ->
                let h'' = fillHolesInHeap keySubst ctx s h''
                Mutation(h, h'')
        | (HigherOrderApplication _ as h), Defined(r, h')
        | (RecursiveApplication _ as h), Defined(r, h') ->
            assert(not r)
            let h' = fillHolesInHeap keySubst ctx s h'
            Mutation(h, h')
        | Mutation(h, h'), Defined(r, h'') ->
            // TODO: this is probably wrong!
            assert(not r)
            Mutation(h, composeDefinedHeaps updateHeap keySubst ctx false s h' h'')

    and composeStacksOf ctx state state' =
        let state'Bottom, state'RestStack, state'RestFrames = State.bottomAndRestFrames state'
        let state2 = MappedStack.fold (fillAndMutateStackLocation ctx state) state state'Bottom  // apply effect of bottom frame
        let state3 = {state2 with frames = State.concatFrames state'RestFrames state2.frames}    // add rest frames
        MappedStack.fold (fillAndMutateStackLocation ctx state) state3 state'RestStack           // fill and copy effect of rest frames

    and composeHeapsOf ctx state heap =
        composeGeneralizedHeaps readHeap updateHeap fillHole ctx heapOf withHeap state heap

    and composeStaticsOf ctx state statics =
        composeGeneralizedHeaps readStatics updateStatics substituteTypeVariables ctx staticsOf withStatics state statics

    and composeStates ctx state state' =
        let stateWithNewFrames = composeStacksOf ctx state state'
        let stateWithOldFrames = {stateWithNewFrames with stack = state.stack; frames = state.frames}
        let heap = composeHeapsOf ctx stateWithOldFrames state'.heap
        let statics = composeStaticsOf ctx stateWithOldFrames state'.statics
        assert(state'.typeVariables |> snd |> Stack.isEmpty)
        let pc = List.map (fillHoles ctx stateWithOldFrames) state'.pc |> List.append stateWithOldFrames.pc
        { stateWithNewFrames with heap = heap; statics = statics; pc = pc }

// ------------------------------- High-level read/write -------------------------------

    and deref metadata state location =
        hierarchicalAccess true true npeTerm snd metadata state location

    and readBlockField metadata blockTerm fieldName fieldType =
        accessBlockField true metadata snd blockTerm fieldName fieldType

    and derefWithoutValidation metadata state location =
        hierarchicalAccess false true (fun _ _ _ -> __unreachable__()) snd metadata state location |> fst

    and private update updateValue metadata state reference = hierarchicalAccess true false npeTerm updateValue metadata state reference

    and mutate metadata state reference value =
        assert(value <> Nop)
        update (always value) metadata state reference

// ------------------------------- Referencing -------------------------------

    and referenceLocalVariable metadata location =
        StackRef metadata location []

    let referenceStaticField metadata targetType fieldName fieldType =
        StaticRef metadata targetType [BlockField(fieldName, fieldType)]

    let private checkIndices mtd state arrayRef (indices : term list) k =
        let intToTerm i = makeNumber mtd i
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
        k (conjunction mtd bounds |> unguard |> merge, state'')))

    let referenceArrayIndex metadata state arrayRef (indices : term list) =
        Logger.trace "!!! referenceArrayIndex, ref: %O" arrayRef
        let reference state = function
            | {term = Ref(RefNullAddress, _) } as arrayRef -> (arrayRef, state)
            | arrayRef ->
                Common.statedConditionalExecutionWithMerge state
                    (fun state k -> checkIndices metadata state arrayRef indices k)
                    (fun state k ->
                        let location = Arrays.makeIndexArray metadata (fun i -> indices.[i]) indices.Length
                        let elemType = baseTypeOfRef arrayRef |> elementType // TODO: add getting type of StackRef when stackalloc will be implemented
                        let result = referenceSubLocations arrayRef [ArrayIndex(location, elemType)]
                        k (result, state))
                    (fun state k ->
                        let exn, state = State.createInstance metadata typeof<System.IndexOutOfRangeException> [] state
                        k (Error metadata exn, state))
        guardedErroredStatedApply reference state arrayRef

// ------------------------------- State layer -------------------------------

    let () =
        State.readHeap <- readHeap
        State.readStatics <- readStatics
        State.readTerm <- readTerm
        State.fillHoles <- fillHoles

// ------------------------------- Allocation -------------------------------

    let freshHeapLocation metadata =
        Concrete metadata ([freshAddress()]) pointerType

    let allocateOnStack metadata s key typ term =
        let oldFrame = Stack.peek s.frames.f
        let newStack = pushToCurrentStackFrame s key term
        let newEntries = { key = key; mtd = metadata; typ = typ }
        let stackFrames = Stack.updateHead s.frames.f { oldFrame with entries = newEntries :: oldFrame.entries }
        { s with stack = newStack; frames = { s.frames with f = stackFrames } }

    let private allocateInDefinedHeap (h : 'a heap) memoryCell term =
        Heap.add memoryCell term h

    let rec private allocateInGeneralizedHeap memoryCell term = function
        | Defined(r, h) -> allocateInDefinedHeap h memoryCell term |> Defined r
        | Composition _
        | RecursiveApplication _
        | HigherOrderApplication _ as h ->
            let mutatedHeap = allocateInDefinedHeap Heap.empty memoryCell term
            Mutation(h, mutatedHeap)
        | Mutation(gh, h) -> Mutation(gh, allocateInDefinedHeap h memoryCell term)
        | Merged gvh ->
            commonGuardedMapk (fun h k -> k <| allocateInGeneralizedHeap memoryCell term h) gvh
                (fun gvh ->
                    let g, h = List.unzip gvh
                    mergeGeneralizedHeaps (fun _ _ _ _ -> __unreachable__()) g h) id

    let allocateInHeap metadata s address baseType sightType term : term * state =
        let ref = HeapRef metadata address baseType sightType []
        let fql = makeTopLevelFQL HeapTopLevelHeap (address, baseType)
        let memoryCell = makeKey address fql baseType
        ref, { s with heap = allocateInGeneralizedHeap memoryCell term s.heap }

    let allocateString metadata state string =
        let address = freshHeapLocation metadata
        let fql = makeTopLevelFQL HeapTopLevelHeap (address, String)
        Strings.makeConcreteStringStruct metadata string fql |> allocateInHeap metadata state address String String

    let mkDefaultStatic metadata state targetType fql =
        let defaultValue metadata _ typ fql' = defaultOf metadata typ fql'
        let mkField, state =
            if targetType = String then
                let emptyStringRef, state = allocateString metadata state System.String.Empty
                let mkStringField metadata name typ fql' =
                    if name.ToString() = "Empty" then emptyStringRef
                    else defaultValue metadata name typ fql'
                mkStringField, state
            else defaultValue, state
        mkBlock metadata true mkField targetType fql, state

    let allocateInStaticMemory _ (s : state) typ term =
        let memoryCell = makeTopLevelKey HeapTopLevelStatics typ typ
        { s with statics = allocateInGeneralizedHeap memoryCell term s.statics }

    let makeSymbolicThis metadata state token typ =
        let isRef = concreteIsReferenceType typ // TODO: "this" can be type variable, so we need to branch by "isValueType" condition
        let thisKey = if isRef then ThisKey token else SymbolicThisKey token
        let fql = HeapTopLevelStack thisKey, []
        let thisStackRef = makeFQLRef metadata fql
        let liSource = lazyInstantiation thisStackRef None
        let instance = makeSymbolicInstance metadata liSource "this" typ (Some fql)
        if isRef
            then instance, state, false
            else
                let state = State.newStackFrame metadata state (EmptyIdentifier()) [(thisKey, Specified instance, typ)]
                thisStackRef, state, true

// --------------------------------------- Is Location Initialized Check ---------------------------------------

    [<StructuralEquality;NoComparison>]
    type internal keyInitializedSource<'a when 'a : equality> =
        {heap : 'a generalizedHeap; key : 'a memoryCell; getter : (state -> 'a generalizedHeap) transparent; fillHolesInKey : (compositionContext -> state -> 'a -> 'a) transparent }
        interface IStatedSymbolicConstantSource with
            override x.SubTerms = seq []

    let private mkKeyGuard mtd fillHolesInKey getter heap (key : 'a memoryCell) =
        Constant mtd (IdGenerator.startingWith "hasKey#") ({ heap = heap; key = key; getter = {v=getter}; fillHolesInKey = {v=fillHolesInKey} } : 'a keyInitializedSource) Bool

    let private guardOfDefinedHeap mtd fillHolesInKey getter key r (h : 'key heap) =
        if Heap.contains key h then Merging.guardOf h.[key]
        elif r then False
        else mkKeyGuard mtd fillHolesInKey getter (Defined r h) key

    let rec private guardOfHeap (exploredRecursiveCodeLocs : ImmutableHashSet<ICodeLocation>) mtd fillHolesInKey getter key = function
        | Defined(r, h) -> guardOfDefinedHeap mtd fillHolesInKey getter key r h
        | Merged ghs -> guardedMap (guardOfHeap exploredRecursiveCodeLocs mtd fillHolesInKey getter key) ghs
        | Mutation(h, h') ->
            guardOfHeap exploredRecursiveCodeLocs mtd fillHolesInKey getter key h ||| guardOfDefinedHeap mtd fillHolesInKey getter key false h'
        | Composition(s, ctx, h) ->
            let filledKey = { key with key = fillHolesInKey ctx s key.key }
            guardOfHeap exploredRecursiveCodeLocs mtd fillHolesInKey getter key (getter s) ||| guardOfHeap exploredRecursiveCodeLocs mtd fillHolesInKey getter filledKey h
        | RecursiveApplication(codeLoc, _) when exploredRecursiveCodeLocs.Contains codeLoc -> False
        | RecursiveApplication(codeLoc, _) ->
            match Database.querySummary codeLoc with
            | Some summary ->
                guardOfHeap (exploredRecursiveCodeLocs.Add codeLoc) mtd fillHolesInKey getter key <| getter summary.state
            | None -> True
        | HigherOrderApplication _ as h ->
            mkKeyGuard mtd fillHolesInKey getter h key

    let private keyInitialized mtd key fillHolesInKey getter heap =
        guardOfHeap ImmutableHashSet<ICodeLocation>.Empty mtd fillHolesInKey getter key heap

    let internal termTypeInitialized mtd termType state =
        let key = makeTopLevelKey HeapTopLevelStatics termType termType
        keyInitialized mtd key substituteTypeVariables staticsOf state.statics

    let internal termLocInitialized mtd loc state =
        keyInitialized mtd loc fillHoles heapOf state.heap

// ------------------------------- Compositions of constants -------------------------------

    type lazyInstantiation<'a when 'a : equality> with
        interface IExtractingSymbolicConstantSource with
            override x.ComposeWithoutExtractor ctx state =
                let state' =
                    match x.heap with
                    | Some heap ->
                        // TODO: make it more effective (use lower-level functions to access heap directly instead of creating fresh state)
                        match x.location.term with // TODO: get rid of box someday
                        | Ref(RefTopLevelHeap _, _) -> { State.empty with heap = composeHeapsOf ctx state (box heap :?> term generalizedHeap) }
                        | Ref(RefTopLevelStatics _, _) -> { State.empty with statics = composeStaticsOf ctx state (box heap :?> termType generalizedHeap) }
                        | _ -> __notImplemented__()
                    | None -> state
                let loc = fillHoles ctx state x.location
                derefWithoutValidation ctx.mtd state' loc
            override x.Compose ctx state =
                (x :> IExtractingSymbolicConstantSource).ComposeWithoutExtractor ctx state |> x.extractor.Extract

    type keyInitializedSource<'a when 'a : equality> with
        interface IStatedSymbolicConstantSource with
            override x.Compose ctx state =
                keyInitialized ctx.mtd x.key x.fillHolesInKey.v x.getter.v (x.getter.v state)
