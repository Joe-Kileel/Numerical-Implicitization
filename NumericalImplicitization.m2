newPackage("NumericalImplicitization",
    Headline => "a package for computing numerical invariants of images of varieties",
    Version => "1.1.0",
    Date => "January 16, 2019",
    Authors => {
        {Name => "Justin Chen",
	 Email => "jchen646@math.gatech.edu",
         HomePage => "https://people.math.gatech.edu/~jchen646/"},
        {Name => "Joe Kileel",
	 Email => "jkileel@math.princeton.edu",
	 HomePage => "https://web.math.princeton.edu/~jkileel/"}
        },
    PackageImports => {},
    PackageExports => {"NumericalAlgebraicGeometry"},
    Reload => true,
    DebuggingMode => true
    )
    export {
        "numericalSourceSample",
        "numericalImageSample",
        "numericalNullity",
        "Precondition",
	"SVDGap",
        "numericalImageDim",
        "numericalHilbertFunction",
        "IsGraded",
	"NumericalInterpolationTable",
        "hilbertFunctionArgument",
        "hilbertFunctionValue",
        "imagePoints",
        "interpolationBasis",
        "interpolationSVD",
        "interpolationMatrix",
	"extractImageEquations",
        "AttemptExact",
	"numericalImageDegree",
        "DoRefinements",
	"DoTraceTest",
        "MaxAttempts",
	"MaxPoints",
	"MaxThreads",
	"Repeats",
        "TraceThreshold",
	"PseudoWitnessSet",
        "isCompletePseudoWitnessSet",
        "sourceEquations",
        "sourceSlice",
        "generalCombinations",
        "imageSlice",
        "witnessPointPairs",
        "traceTest",
	"isOnImage",
        "numericalEval"
    }

-- software options: default is M2engine throughout

NumericalInterpolationTable = new Type of HashTable
NumericalInterpolationTable.synonym = "numerical interpolation table"
globalAssignment NumericalInterpolationTable
net NumericalInterpolationTable := T -> (
    	(net ofClass class T | ", indicating") ||
	("the space of degree " | (toString T.hilbertFunctionArgument) | 
        " forms in the ideal of the image has dimension " | (toString T.hilbertFunctionValue))
)

PseudoWitnessSet = new Type of HashTable
PseudoWitnessSet.synonym = "pseudo-witness set"
globalAssignment PseudoWitnessSet
net PseudoWitnessSet := W -> (
    	(net ofClass class W | ", indicating") ||
	("the image has degree " | (toString W.degree))
)


checkRings = method(Options => {symbol IsGraded => true})
-- Turns F to a matrix of polynomials, checks if the rings of F and I agree and have floating point arithmetic, and converts F, I to the affine cone if IsGraded is false
checkRings (Matrix, Ideal) := Sequence => opts -> (F, I) -> (
    k := coefficientRing ring I;
    if not numrows F == 1 then error "Expected map to be given by a 1-row matrix of polynomials";
    if not ring F === ring I then error "Expected same rings for ideal and map";
    if not instance(class(1_k), InexactFieldFamily) then error "Expected coefficient field with floating point arithmetic";
    if not opts.IsGraded then (
        t := getSymbol "t";
        R := k(monoid[append(gens ring I, t)]);
        toR := map(R, ring I);
        ((last gens R)*(toR F | matrix{{1_R}}), toR(I))
        -- ((last gens R)*append(apply(F, f -> toR(f)), 1_R), toR(I))
    ) else (F, I)
)


numericalSourceSample = method(Options => {Software => M2engine}) --outputs a list of random sample points of V(I)
numericalSourceSample (Ideal, Thing, ZZ) := List => opts -> (I, W, sampleSize) -> (
    if I == 0 then return apply(sampleSize, i -> point{apply(gens(ring(I)), x -> random coefficientRing(ring(I)))});
    samplePoints := toList(1..sampleSize)/(i -> sample(W));
    if precision(ring(I)) <= precision(ring(first (first samplePoints)#Coordinates)) then return samplePoints;
    refine(polySystem(I_*), samplePoints, Bits => precision(ring(I)))
)
numericalSourceSample (Ideal, Thing) := List => opts -> (I, W) -> numericalSourceSample(I, W, 1, opts)
numericalSourceSample (Ideal, ZZ) := List => opts -> (I, sampleSize) -> numericalSourceSample(I, if I == 0 then null else first components(numericalIrreducibleDecomposition(I, Software => opts.Software)), sampleSize)
numericalSourceSample Ideal := List => opts -> I -> numericalSourceSample(I, 1, opts)

    
numericalImageSample = method(Options => options checkRings ++ options numericalSourceSample)
numericalImageSample (Matrix, Ideal, ZZ) := List => opts -> (F, I, sampleSize) -> (
    (F, I) = checkRings(F, I, IsGraded => opts.IsGraded);
    numericalEval(F, numericalSourceSample(I, sampleSize, Software => opts.Software), false) /point
)
numericalImageSample (Matrix, Ideal) := List => opts -> (F, I) -> numericalImageSample(F, I, 1, opts)
numericalImageSample (List, Ideal, ZZ) := List => opts -> (F, I, sampleSize) -> numericalImageSample(matrix{F}, I, sampleSize, opts)
numericalImageSample (List, Ideal) := List => opts -> (F, I) -> numericalImageSample(matrix{F}, I, opts)
numericalImageSample (RingMap, Ideal, ZZ) := List => opts -> (F, I, sampleSize) -> numericalImageSample(F.matrix, I, sampleSize, opts)
numericalImageSample (RingMap, Ideal) := List => opts -> (F, I) -> numericalImageSample(F.matrix, I, opts)


numericalDimensions = method(Options => options numericalImageSample)
numericalDimensions (Matrix, Ideal, Thing) := List => opts -> (F, I, p) -> ( --outputs {dim(V(I)), dim(F(V(I))}
    (F, I) = checkRings(F, I, IsGraded => opts.IsGraded);
    if p === {} then p = first numericalSourceSample(I, Software => opts.Software);
    p0 := 1/norm(2, matrix p)*(matrix p);
    dF := sub(transpose(jacobian(F)), p0);
    if I == 0 then return {#gens ring I, #gens ring I - numericalNullity(dF, false)};
    sourceJacobian := sub(transpose(jacobian(I)), p0);
    sourceDim := numericalNullity(sourceJacobian, false);
    {sourceDim, sourceDim - numericalNullity(sourceJacobian || dF, false)}
)
numericalDimensions (Matrix, Ideal) := ZZ => opts -> (F, I) -> numericalDimensions(F, I, {}, opts)


numericalImageDim = method(Options => options numericalImageSample)
numericalImageDim (Matrix, Ideal, Point) := ZZ => opts -> (F, I, p) -> last numericalDimensions(F, I, p, opts)
numericalImageDim (Matrix, Ideal) := ZZ => opts -> (F, I) -> last numericalDimensions(F, I, opts)
numericalImageDim (List, Ideal, Point) := ZZ => opts -> (F, I, p) -> last numericalDimensions(matrix{F}, I, p, opts)
numericalImageDim (List, Ideal) := ZZ => opts -> (F, I) -> last numericalDimensions(matrix{F}, I, opts)
numericalImageDim (RingMap, Ideal, Point) := ZZ => opts -> (F, I, p) -> last numericalDimensions(F.matrix, I, p, opts)
numericalImageDim (RingMap, Ideal) := ZZ => opts -> (F, I) -> last numericalDimensions(F.matrix, I, opts)


-- converts M to a list of 1-element lists of row matrices (to normalize rows easily)
-- listForm satisfies M == matrix listForm M, and this conversion is fast
listForm Matrix := A -> apply(entries A, r -> {matrix{r}})


rowScale := (L, s) -> matrix flatten apply(L, r -> if r#0 == 0 then {} else {(s/norm(2,r#0))*r}) -- deletes any zero rows
-- doubleScale := L -> transpose rowScale((entries transpose rowScale(L,1))/(r -> {matrix{r}}), sqrt(#L/(numcols(L#0#0))))


numericalNullity = method(Options => {symbol SVDGap => 1e6, Verbose => false, symbol Precondition => false})
numericalNullity (List, Boolean) := List => opts -> (M, keepSVD) -> (
    if matrix M == 0 then return if keepSVD then {numcols M#0#0, 0} else numcols M#0#0;
    if opts.Verbose then (
        A := if opts.Precondition then (
            print "Performing normalization preconditioning ...";
	    time rowScale(M, 1)
        ) else matrix M;
	print "Computing numerical kernel ...";
	time (S, U, Vt) := SVD A; -- do not use DivideConquer => true!
    ) else (
        A = if opts.Precondition then rowScale(M, 1) else matrix M;
        (S, U, Vt) = SVD A;
    );
    largestGap := (#S, opts.SVDGap);
    for i from 1 to #S-1 do (
        if S#i == 0 then (
            if first largestGap == #S then largestGap = (i, "infinity");
            break;
        ) else if S#(i-1)/S#i > last largestGap then largestGap = (i, S#(i-1)/S#i);
    );
    if keepSVD then {numcols A - first largestGap, (S, U, Vt)} else numcols A - first largestGap
)
numericalNullity (Matrix, Boolean) := ZZ => opts -> (M, keepSVD) -> numericalNullity(listForm M, keepSVD, opts)
numericalNullity Matrix := ZZ => opts -> M -> numericalNullity(M, false, opts)


numericalHilbertFunction = method(Options => {
    symbol IsGraded => true, 
    symbol Precondition => true,
    Software => M2engine,
    symbol SVDGap => 1e6,
    Verbose => true})
numericalHilbertFunction (Matrix, Ideal, List, ZZ) := NumericalInterpolationTable => opts -> (F, I, sampleImagePoints, d) -> ( --outputs a degree d interpolation table for F(V(I))
    (F, I) = checkRings(F, I, IsGraded => opts.IsGraded);
    if not opts.IsGraded then sampleImagePoints = apply(sampleImagePoints, p -> {append(p#Coordinates, 1_(coefficientRing ring I))});
    y := getSymbol "y";
    allMonomials := basis(d, (coefficientRing ring I)(monoid[y_0..y_(numcols F-1)]));
    N := numcols allMonomials;
    if #sampleImagePoints < N then (
        if opts.Verbose then (
            print "Sampling image points ...";
            time sampleImagePoints = join(sampleImagePoints, numericalImageSample(F, I, N - #sampleImagePoints, Software => opts.Software));
        ) else sampleImagePoints = join(sampleImagePoints, numericalImageSample(F, I, N - #sampleImagePoints, Software => opts.Software));
    );
    sampleImagePoints = apply(sampleImagePoints/matrix, p -> 1/norm(2,p)*p);
    if opts.Verbose then (
        print "Creating interpolation matrix ...";
        time A := apply(sampleImagePoints, p -> {sub(allMonomials, p)});
    ) else A = apply(sampleImagePoints, p -> {sub(allMonomials, p)});
    interpolationData := numericalNullity(A, true, Precondition => opts.Precondition, SVDGap => opts.SVDGap, Verbose => opts.Verbose);
    new NumericalInterpolationTable from {
        symbol hilbertFunctionArgument => d,
        symbol hilbertFunctionValue => first interpolationData,
        symbol imagePoints => VerticalList sampleImagePoints,
	symbol interpolationBasis => allMonomials,
        symbol interpolationSVD => last interpolationData,
        symbol interpolationMatrix => matrix A,
	symbol map => F
    }
)
numericalHilbertFunction (Matrix, Ideal, ZZ) := NumericalInterpolationTable => opts -> (F, I, d) -> numericalHilbertFunction(F, I, {}, d, opts)
numericalHilbertFunction (List, Ideal, List, ZZ) := NumericalInterpolationTable => opts -> (F, I, sampleImagePoints, d) -> numericalHilbertFunction(matrix{F}, I, sampleImagePoints, d, opts)
numericalHilbertFunction (List, Ideal, ZZ) := NumericalInterpolationTable => opts -> (F, I, d) -> numericalHilbertFunction(matrix{F}, I, {}, d, opts)
numericalHilbertFunction (RingMap, Ideal, List, ZZ) := NumericalInterpolationTable => opts -> (F, I, sampleImagePoints, d) -> numericalHilbertFunction(F.matrix, I, sampleImagePoints, d, opts)
numericalHilbertFunction (RingMap, Ideal, ZZ) := NumericalInterpolationTable => opts -> (F, I, d) -> numericalHilbertFunction(F.matrix, I, {}, d, opts)


realPartMatrix := A -> matrix apply(entries A, r -> r/realPart)
imPartMatrix := A -> matrix apply(entries A, r -> r/imaginaryPart)


extractImageEquations = method(Options => {symbol Threshold => 8, symbol AttemptExact => false})
extractImageEquations NumericalInterpolationTable := Matrix => opts -> T -> (
    if not opts.AttemptExact then (
        (V, mons) := (last T.interpolationSVD, transpose T.interpolationBasis);
        n := numrows V;
        clean(10.0^(-opts.Threshold), sub(V^{n-T.hilbertFunctionValue..n-1}, ring mons)*mons)
    ) else (
        A := T.interpolationMatrix;
        B := random(RR)*realPartMatrix A + random(RR)*imPartMatrix A;
        C := matrix apply(entries B, r -> r/(e -> lift(round(10^(1+opts.Threshold)*round(opts.Threshold, e)), ZZ)));
        D := submatrix(LLL(id_(ZZ^(numcols C)) || C), toList (0..<numcols T.interpolationBasis), toList(0..<T.hilbertFunctionValue));
        transpose(T.interpolationBasis*sub(D, ring T.interpolationBasis))
    )
)
extractImageEquations (Matrix, Ideal, ZZ) := Matrix => opts -> (F, I, d) -> extractImageEquations(numericalHilbertFunction(F, I, d), opts)
extractImageEquations (List, Ideal, ZZ) := Matrix => opts -> (F, I, d) -> extractImageEquations(numericalHilbertFunction(matrix{F}, I, d), opts)
extractImageEquations (RingMap, Ideal, ZZ) := Matrix => opts -> (F, I, d) -> extractImageEquations(numericalHilbertFunction(F.matrix, I, d), opts)


round (ZZ, ZZ) := ZZ => (n, x) -> x
round (ZZ, CC) := CC => (n, x) -> round(n, realPart x) + ii*round(n, imaginaryPart x)
round (ZZ, BasicList) := BasicList => (n, L) -> L/round_n
round (ZZ, Matrix) := Matrix => (n, M) -> matrix(entries M/round_n)
round (ZZ, RingElement) := RingElement => (n, f) -> (
    C := coefficients f;
    ((C#0)*round(n, lift(C#1, coefficientRing ring f)))_(0,0)
)


numericalImageDegree = method(Options => {
    symbol DoRefinements => false,
    symbol DoTraceTest => true,
    IsGraded => true,
    symbol MaxAttempts => 5,
    symbol MaxPoints => infinity,
    symbol MaxThreads => 1,
    Software => M2engine,
    symbol Repeats => 3,
    symbol TraceThreshold => 1e-5,
    symbol Threshold => 5,
    Verbose => true})
numericalImageDegree (Matrix, List, List, Thing) := PseudoWitnessSet => opts -> (F, sourceData, pointPairs, sliceData) -> ( --outputs a pseudo-witness set for F(V(I))
    local imagePointString, local pairTable, local startSystem;
    I := sourceData#0;
    W := sourceData#1;
    y := getSymbol "y";
    targetRing := (coefficientRing(ring(I)))(monoid[y_1..y_(numcols F)]);
    if #pointPairs == 0 then error "Expected source point";
    sourcePoint := pointPairs#0#0;
    dims := numericalDimensions(F, I, sourcePoint);
    numAttempts := 0;
    traceResult := opts.TraceThreshold + 1;
    while not traceResult < opts.TraceThreshold and numAttempts < opts.MaxAttempts do (
        if numAttempts > 0 and W === {} and sliceData === null then (
	    if not I == 0 then W = first components numericalIrreducibleDecomposition(I, Software => opts.Software);
	    sourcePoint = first numericalSourceSample(I, W);
	);       
        if sliceData === null then (
            pullbackSliceData := randomCombinations(F, last dims, false);
            sliceTranslation := sub(matrix{last pullbackSliceData}, matrix sourcePoint);
            pullbackSlice := (last pullbackSliceData) - flatten entries sliceTranslation;
            sliceCoefficients := sub((first pullbackSliceData) || (-1)*sliceTranslation, targetRing);
        ) else (
            if numAttempts == 0 then (
                pullbackSlice = flatten entries sub(sliceData, F);
                sliceCoefficients = sub(fold(flatten entries sliceData /coefficients/last, L -> L#0 | L#1), targetRing);
                if not all(pointPairs, pair -> clean((10.0)^(-opts.Threshold), (matrix last pair | matrix{{1_(coefficientRing(ring(I)))}}) * sub(sliceCoefficients, coefficientRing(ring(I)))) == 0) then error "Expected input points to lie on input slice";
            );
        );
        fiberSlice := if first dims > last dims then (
            newFiberSlice := last randomCombinations(vars(ring(I)), first dims - last dims, true);
            newFiberSlice - flatten entries sub(matrix{newFiberSlice}, matrix sourcePoint)
        ) else {};
        squaredUpSource := if I == 0 then {} else last randomCombinations(gens I, #gens(ring(I)) - first dims, false);
	newStartSystem := squaredUpSource | fiberSlice | pullbackSlice;
        newPairs := if numAttempts > 0 then numericalEval(F, myTrack(startSystem, newStartSystem, (values pairTable)/first, opts), true) else pointPairs/(pair -> (pair#0, matrix pair#1));
        pairTable = new MutableHashTable;
        for newPair in newPairs do (
            imagePointString = toString round(opts.Threshold, last newPair);
            if not pairTable#?imagePointString then pairTable#imagePointString = newPair;
        );       
	startSystem = newStartSystem;
        pointPairs = monodromyLoop(F, last dims, startSystem, pairTable, opts);
	if not opts.DoTraceTest then break;
	if opts.Verbose then print("Running trace test ...");
	traceResult = traceTest(F, last dims, pointPairs, startSystem, opts);
	if not traceResult < opts.TraceThreshold and opts.Verbose then print("Failed trace test! Trace: " | toString traceResult);
    	numAttempts = numAttempts + 1;
    );
    if opts.Verbose then (
	if traceResult > opts.TraceThreshold then (
            print("Degree of image should be at least " | #pointPairs);
            print("Consider changing parameters (Repeats, MaxAttempts, Threshold) or reparametrizing for a better result.");
            -- Alternatively, consider increasing precision (e.g. changing ground field to CC_100).
        );
    );
    if opts.DoRefinements then (
        if opts.Verbose then print "Refining solutions...";
        refinedPts := refine(pointPairs/first, startSystem, Bits => precision(ring(I)));
        pointPairs = numericalEval(F, refinedPts, true);
    );
    new PseudoWitnessSet from {
        symbol isCompletePseudoWitnessSet => traceResult < opts.TraceThreshold,
        symbol degree => #pointPairs,
        symbol map => F,
        symbol sourceEquations => I,
        symbol sourceSlice => transpose matrix{fiberSlice},
        symbol generalCombinations => transpose matrix{squaredUpSource},
        symbol imageSlice => ((vars targetRing) | matrix{{1_targetRing}})*sliceCoefficients,
        symbol witnessPointPairs => VerticalList apply(pointPairs, pair -> (pair#0, point pair#1)),
        symbol witnessSet => W, 
	symbol trace => traceResult
    }
)
numericalImageDegree(Matrix, Ideal, List, Thing) := PseudoWitnessSet => opts -> (F, I, pointPairs, L) -> ( -- points are specified, did not try to find witness set for V(I)
    numericalImageDegree(F, {I, {}}, pointPairs, L, opts)
)
numericalImageDegree(Matrix, Ideal, Point, Thing) := PseudoWitnessSet => opts -> (F, I, p, L) -> (
    (F, I) = checkRings(F, I, IsGraded => opts.IsGraded);
    if not opts.IsGraded then p = point{append(p#Coordinates, 1_(coefficientRing(ring(I))))};
    numericalImageDegree(F, I, numericalEval(F, {p}, true), L, opts)
)
numericalImageDegree(Matrix, Ideal, Point) := PseudoWitnessSet => opts -> (F, I, p) -> numericalImageDegree(F, I, p, null, opts)
numericalImageDegree (Matrix, Ideal) := PseudoWitnessSet => opts -> (F, I) -> (
    (F, I) = checkRings(F, I, IsGraded => opts.IsGraded);
    if opts.Verbose then print "Sampling point in source ...";
    W := if I == 0 then null else first components numericalIrreducibleDecomposition(I, Software => opts.Software);
    numericalImageDegree(F, {I, W}, numericalEval(F, numericalSourceSample(I, W), true), null, opts)
)
numericalImageDegree (List, List, List, Thing) := PseudoWitnessSet => opts -> (F, sourceData, pointPairs, sliceData) -> numericalImageDegree(matrix{F}, sourceData, pointPairs, sliceData, opts)
numericalImageDegree(List, Ideal, List, Thing) := PseudoWitnessSet => opts -> (F, I, pointPairs, L) -> numericalImageDegree(matrix{F}, I, pointPairs, L, opts)
numericalImageDegree(List, Ideal, Point, Thing) := PseudoWitnessSet => opts -> (F, I, p, L) -> numericalImageDegree(matrix{F}, I, p, L, opts)
numericalImageDegree(List, Ideal, Point) := PseudoWitnessSet => opts -> (F, I, p) -> numericalImageDegree(matrix{F}, I, p, opts)
numericalImageDegree (List, Ideal) := PseudoWitnessSet => opts -> (F, I) -> numericalImageDegree(matrix{F}, I, opts)
numericalImageDegree (RingMap, List, List, Thing) := PseudoWitnessSet => opts -> (F, sourceData, pointPairs, sliceData) -> numericalImageDegree(F.matrix, sourceData, pointPairs, sliceData, opts)
numericalImageDegree(RingMap, Ideal, List, Thing) := PseudoWitnessSet => opts -> (F, I, pointPairs, L) -> numericalImageDegree(F.matrix, I, pointPairs, L, opts)
numericalImageDegree(RingMap, Ideal, Point, Thing) := PseudoWitnessSet => opts -> (F, I, p, L) -> numericalImageDegree(F.matrix, I, p, L, opts)
numericalImageDegree(RingMap, Ideal, Point) := PseudoWitnessSet => opts -> (F, I, p) -> numericalImageDegree(F.matrix, I, p, opts)
numericalImageDegree (RingMap, Ideal) := PseudoWitnessSet => opts -> (F, I) -> numericalImageDegree(F.matrix, I, opts)


myTrack = method(Options => options numericalImageDegree)
myTrack (List, List, List) := List => opts -> (startSystem, targetSystem, startSolutions) -> (
    randomGamma := random(coefficientRing(ring(first(startSystem))));
    startSystem = polySystem startSystem;
    targetSystem = polySystem targetSystem;
    if #startSolutions > max(20, 2*opts.MaxThreads) and opts.MaxThreads > 1 then ( -- buggy
        startSolutionsList := pack(ceiling(#startSolutions/opts.MaxThreads), startSolutions);
        threadList := {};
        for paths in startSolutionsList do (
            threadList = append(threadList, schedule(track, (startSystem, targetSystem, paths, gamma => randomGamma, Software => opts.Software)));
        );
        while not all(threadList, isReady) do sleep 1;
        targetSolutions := flatten(threadList/taskResult);
        if opts.Verbose then print("Finished tracking " | #targetSolutions | " paths in parallel");
    ) else targetSolutions = track(startSystem, targetSystem, startSolutions, gamma => randomGamma, Software => opts.Software);
    goodSols := select(targetSolutions, p -> p#?SolutionStatus and p#SolutionStatus == Regular);
    if opts.Verbose and #goodSols < #startSolutions then print("Paths going to infinity: " | #startSolutions - #goodSols | " out of " | #startSolutions);
    goodSols
)


numericalEval = method()
numericalEval (Matrix, List, Boolean) := List => (F, upstairsPoints, includeUpstairs) -> (
    evalPts := upstairsPoints/(p -> (p, sub(F, matrix p)));
    if includeUpstairs then evalPts else evalPts/last
)


randomCombinations = method() -- outputs a list of c random linear combinations of polys
randomCombinations (Matrix, ZZ, Boolean) := List => (polys, c, isAffine) -> ( -- polys should be a row matrix
    R := ring polys;
    if isAffine then polys = polys | matrix{{10_R}};
    randomCoefficients := random(R^(numcols polys), R^c);
    (randomCoefficients, flatten entries(polys*randomCoefficients))
)
randomCombinations (List, ZZ, Boolean) := List => (polys, c, keepCoeffs) -> (
    C := coefficientRing(ring(first polys));
    randomCoefficients := random(C^c, C^#polys);
    newpolys := flatten entries(promote(randomCoefficients, ring(first polys)) * transpose(matrix{polys}));
    if keepCoeffs then (randomCoefficients, newpolys) else newpolys
)


monodromyLoop = method(Options => options numericalImageDegree)
monodromyLoop (Matrix, ZZ, List, MutableHashTable) := List => opts -> (F, imageDim, startSystem, pairTable) -> (
    numRepetitiveMonodromyLoops := 0;
    if opts.Verbose then print "Tracking monodromy loops ...";
    while numRepetitiveMonodromyLoops < opts.Repeats do (
        previousNumImagePoints := #values pairTable;
        intermediateSystem1 := drop(startSystem, -imageDim) | last randomCombinations(F, imageDim, true);
        intermediateSolutions1 := myTrack(startSystem, intermediateSystem1, (values pairTable)/first, opts);
        if #intermediateSolutions1 > 0 then (
            endSolutions := myTrack(intermediateSystem1, startSystem, intermediateSolutions1, opts);
            if #endSolutions > 0 then (
                candidatePairs := numericalEval(F, endSolutions, true);
                for newPair in candidatePairs do (
                    imagePointString := toString round(opts.Threshold, last newPair);
                    if not pairTable#?imagePointString then pairTable#imagePointString = newPair;
                );
            );
        );
        if previousNumImagePoints < #values pairTable then numRepetitiveMonodromyLoops = 0
        else numRepetitiveMonodromyLoops = numRepetitiveMonodromyLoops + 1;
        if opts.Verbose then print ("Points found: " | #values pairTable);
        if #values pairTable > opts.MaxPoints then break;
    );
    values pairTable
)


traceTest = method(Options => options numericalImageDegree)
traceTest (Matrix, ZZ, List, List) := RR => opts -> (F, imageDim, intersectionPointPairs, startSystem) -> (
    C := coefficientRing(ring F);
    startUpstairsPoints := intersectionPointPairs/first;
    startDownstairsPoints := intersectionPointPairs/last;
    for translationMagnitude in {1,2,3,4,5,-1,6,-2} do (
        -- if opts.Verbose then print("Translation magnitude: " | toString translationMagnitude);
        randomTranslation := 10^(4-translationMagnitude)*flatten entries(map(C^1, C^(#startSystem - imageDim), 0) | random(C^1, C^imageDim));
        gammas := {random(C), random(C)};
        firstStepSystem := startSystem + (first gammas)*randomTranslation;
        secondStepSystem := startSystem + (last gammas)*randomTranslation;
        firstStepUpstairsPoints := myTrack(startSystem, firstStepSystem, startUpstairsPoints, opts);
        if #firstStepUpstairsPoints == #startUpstairsPoints then (
            secondStepUpstairsPoints := myTrack(startSystem, secondStepSystem, startUpstairsPoints, opts);
            if #secondStepUpstairsPoints == #startUpstairsPoints then (
                firstStepDownstairsPoints := numericalEval(F, firstStepUpstairsPoints, false);
                secondStepDownstairsPoints := numericalEval(F, secondStepUpstairsPoints, false);
                traceList := (1/first gammas)*(firstStepDownstairsPoints - startDownstairsPoints) - (1/last gammas)*(secondStepDownstairsPoints - startDownstairsPoints);
                return norm(2,sum(traceList))
            );
        );
    );
    infinity
)


isOnImage = method(Options => {
    IsGraded => true,
    MaxThreads => 1,
    Software => M2engine,
    Threshold => 5,
    Verbose => true})
isOnImage (PseudoWitnessSet, Point) := Boolean => opts -> (W, q) -> (
    q = matrix if not opts.IsGraded then point{append(q#Coordinates, 1_(ring(first(q#Coordinates))))} else q;
    if not W.isCompletePseudoWitnessSet then print "Warning: not a complete pseudo-witness set! May return false negative.";
    F := W.map;
    I := W.sourceEquations;
    if not ring q === coefficientRing ring I then error "Point must have coordinates in the coefficient ring of the ideal.";
    fiberSlice := flatten entries W.sourceSlice;
    targetVariables := gens ring(W.imageSlice);
    pullbackSlice := flatten entries sub(W.imageSlice, F);
    -- squaredUpSource := if I == 0 then {} else last randomCombinations(gens I, #gens(ring(I)) - #fiberSlice - #pullbackSlice, false);
    squaredUpSource := flatten entries W.generalCombinations;
    startUpstairsPoints := W.witnessPointPairs /first;
    newPullbackSliceData := randomCombinations(F, #pullbackSlice, false);
    sliceCoefficients := first newPullbackSliceData;
    newPullbackSlice := last newPullbackSliceData;
    newPullbackSlice = newPullbackSlice - flatten entries (promote(q, coefficientRing ring I) * sliceCoefficients);
    targetUpstairsPoints := myTrack(squaredUpSource | fiberSlice | pullbackSlice, squaredUpSource | fiberSlice | newPullbackSlice, startUpstairsPoints, opts);
    imagePointTable := hashTable apply(numericalEval(F, targetUpstairsPoints, false), p -> round(opts.Threshold, p) => 0);
    imagePointTable#?(round(opts.Threshold, q))
)
isOnImage (Matrix, Ideal, Point) := Boolean => opts -> (F, I, q) -> isOnImage(numericalImageDegree(F, I, opts), q, opts)
isOnImage (List, Ideal, Point) := Boolean => opts -> (F, I, q) -> isOnImage(matrix{F}, I, q, opts)
isOnImage (RingMap, Ideal, Point) := Boolean => opts -> (F, I, q) -> isOnImage(F.matrix, I, q, opts)


isWellDefined NumericalInterpolationTable := Boolean => T -> (
    -- CHECK DATA STRUCTURE
    -- CHECK KEYS
    K := keys T;
    expectedKeys := set {
        symbol hilbertFunctionArgument,
        symbol hilbertFunctionValue,
        symbol imagePoints,
        symbol interpolationBasis,
        symbol interpolationSVD,
	symbol interpolationMatrix,
        symbol map
    };
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList(K - expectedKeys);
	    missing := toList(expectedKeys - K);
	    if #added > 0 then << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then << "-- missing keys(s): " << toString missing << endl;
        );
        return false
    );
    -- CHECK TYPES
    if not instance(T.hilbertFunctionArgument, ZZ) then (
        if debugLevel > 0 then << "-- expected `hilbertFunctionArgument' to be an integer" << endl;
	return false
    );
    if not instance(T.hilbertFunctionValue, ZZ) then (
        if debugLevel > 0 then << "-- expected `hilbertFunctionValue' to be an integer" << endl;
	return false
    );
    if not instance(T.map, Matrix) then (
        if debugLevel > 0 then << "-- expected `map' to be a matrix" << endl;
	return false
    );
    if not instance(T.interpolationBasis, Matrix) then (
        if debugLevel > 0 then << "-- expected `interpolationBasis' to be a matrix" << endl;
	return false
    );
    if not instance(T.interpolationMatrix, Matrix) then (
        if debugLevel > 0 then << "-- expected `interpolationMatrix' to be a matrix" << endl;
	return false
    );
    if not instance(T.interpolationSVD, Sequence) then (
        if debugLevel > 0 then << "-- expected `interpolationSVD' to be a sequence" << endl;
        return false
    );
    if not instance(first T.interpolationSVD, List) then (
        if debugLevel > 0 then << "-- expected first element of `interpolationSVD' to be a list" << endl;
        return false
    );
    if not all(first T.interpolationSVD, s -> instance(s, RR)) then (
        if debugLevel > 0 then << "-- expected first element of `interpolationSVD' to be a list of singular values" << endl;
        return false
    );
    if not all(drop(T.interpolationSVD, 1), M -> instance(M, Matrix)) then (
        if debugLevel > 0 then << "-- expected second and third elements of `interpolationSVD' to be matrices" << endl;
	return false
    );
    -- CHECK MATHEMATICAL STRUCTURE
    if not unique flatten last degrees T.interpolationBasis === {T.hilbertFunctionArgument} then (
        if debugLevel > 0 then << ("-- expected `interpolationBasis' to consist of monomials of degree " | T.hilbertFunctionArgument) << endl;
        return false
    );
    if not all({coefficientRing ring T.interpolationBasis, ring(T.interpolationSVD#2)}/class, C -> C === ComplexField) then (
        if debugLevel > 0 then << "-- expected ground field to be complex numbers" << endl;
        return false
    );
    numMonomials := binomial(numcols T.map + T.hilbertFunctionArgument - 1, T.hilbertFunctionArgument);
    if not #gens ring T.interpolationBasis === numcols T.map or not numcols T.interpolationBasis === numMonomials then (
        if debugLevel > 0 then << ("-- expected `interpolationBasis' to have " | numMonomials | " monomials in " | #T.map | " variables") << endl;
        return false
    );
    true
)

isWellDefined PseudoWitnessSet := Boolean => W -> (
    -- CHECK DATA STRUCTURE
    -- CHECK KEYS
    K := keys W;
    expectedKeys := set {
        symbol isCompletePseudoWitnessSet, 
        symbol degree, 
        symbol map, 
        symbol sourceEquations, 
        symbol sourceSlice, 
        symbol generalCombinations,
        symbol imageSlice, 
        symbol witnessPointPairs, 
        symbol witnessSet, 
        symbol trace
    };
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList(K - expectedKeys);
	    missing := toList(expectedKeys - K);
	    if #added > 0 then << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then << "-- missing keys(s): " << toString missing << endl;
        );
        return false
    );
    -- CHECK TYPES
    if not instance(W.isCompletePseudoWitnessSet, Boolean) then (
        if debugLevel > 0 then << "-- expected `isCompletePseudoWitnessSet' to be a Boolean" << endl;
	return false
    );
    if not instance(W.degree, ZZ) then (
        if debugLevel > 0 then << "-- expected `degree' to be an integer" << endl;
	return false
    );
    if not instance(W.map, Matrix) then (
        if debugLevel > 0 then << "-- expected `map' to be a matrix" << endl;
	return false
    );
    if not instance(W.sourceEquations, Ideal) then (
        if debugLevel > 0 then << "-- expected `sourceEquations' to be an ideal" << endl;
	return false
    );
    if not instance(W.sourceSlice, Matrix) then (
        if debugLevel > 0 then << "-- expected `sourceSlice' to be a matrix" << endl;
	return false
    );
    if not instance(W.generalCombinations, Matrix) then (
        if debugLevel > 0 then << "-- expected `generalCombinations' to be a matrix" << endl;
	return false
    );
    if not instance(W.imageSlice, Matrix) then (
        if debugLevel > 0 then << "-- expected `imageSlice' to be a matrix" << endl;
	return false
    );
    if not instance(W.witnessPointPairs, List) then (
        if debugLevel > 0 then << "-- expected `witnessPointPairs' to be a list" << endl;
	return false
    );
    if not all(W.witnessPointPairs, pair -> instance(pair, Sequence)) then (
        if debugLevel > 0 then << "-- expected `witnessPointPairs' to be a list of sequences" << endl;
        return false
    );
    if not all(W.witnessPointPairs, pair -> all(pair, p -> instance(p, Point))) then (
        if debugLevel > 0 then << "-- expected `witnessPointPairs' to be a list of sequences of points" << endl;
        return false
    );
    if not instance(W.trace, RR) then (
        if debugLevel > 0 then << "-- expected `trace' to be a real number" << endl;
	return false
    );
    -- CHECK MATHEMATICAL STRUCTURE
    R := ring W.sourceEquations;
    if not R === ring W.map then (
        if debugLevel > 0 then << "-- expected `map' and `sourceEquations' to have the same ring" << endl;
        return false
    );
    if not instance(class 1_(coefficientRing R), InexactFieldFamily) then (
        if debugLevel > 0 then << "-- expected ground field to have floating point arithmetic" << endl;
        return false
    );
    if not all(W.witnessPointPairs, pair -> #(pair#0#Coordinates) === #gens R and #(pair#1#Coordinates) === #gens ring W.imageSlice) then (
        if debugLevel > 0 then << "-- number of coordinates in `witnessPointPairs' do not match" << endl;
        return false
    );
    if not all(W.witnessPointPairs/first, p -> clean(1e-10, sub(gens W.sourceEquations, matrix p)) == 0) then (
	if debugLevel > 0 then << " -- expected first components of `witnessPointPairs' to satisfy `sourceEquations'" << endl;
	return false
    );
    if not all(W.witnessPointPairs, pair -> clean(1e-10, matrix last pair - sub(W.map, matrix first pair)) == 0) then (
	if debugLevel > 0 then << " -- expected components `witnessPointPairs' to correspond under `map'" << endl;
	return false
    );
    if not all(W.witnessPointPairs/last/matrix, q -> clean(1e-10, sub(W.imageSlice, q)) == 0) then (
	if debugLevel > 0 then << " -- expected second components of `witnessPointPairs' to lie on `imageSlice'" << endl;
	return false
    );
    true
)


beginDocumentation()

--Documention--
--<<docTemplate
doc ///
    Key
    	NumericalImplicitization
    Headline
    	implicitization using numerical algebraic geometry
    Description
    	Text
	    This package supports user-friendly calculation of basic invariants of the image 
            of a polynomial map. The computational techniques (interpolation, homotopy 
            continuation and monodromy) come from numerical algebraic geometry.

	    Many varieties of interest in algebraic geometry and its applications are usefully 
            described as images of polynomial maps, via a parametrization. Implicitization is the
            process of converting a parametric description of a variety into an intrinsic, or implicit,
            description. Classically, implicitization refers to the procedure of computing the defining
            equations of a parametrized variety, and in theory this is accomplished by finding the
            kernel of a ring homomorphism, via Gr&ouml;bner bases. In practice however, 
            symbolic Gr&ouml;bner basis computations are often time consuming, even for 
            medium scale problems, and do not scale well with respect to the size of the input.

	    Despite this, one would often like to know basic information about a parametrized 
            variety, even when symbolic methods are prohibitively expensive. Examples of 
	    such information are discrete invariants such as the 
            @TO2{numericalImageDim, "dimension"}@, the 
	    @TO2{numericalImageDegree, "degree"}@, or 
            @TO2{numericalHilbertFunction, "Hilbert function"}@ 
	    values. Other examples include Boolean tests, for example whether a particular point 
	    @TO2{isOnImage, "lies on"}@ a parametrized variety. The goal of this package is to
            provide such information; in other words to numerically implicitize a parametrized variety.
    
	    {\em NumericalImplicitization} builds on existing numerical algebraic geometry software: 
	    @TO2{NumericalAlgebraicGeometry,"NAG4M2"}@, @TO Bertini@ and 
            @TO PHCpack@. The user may specify any of these to use for path tracking and 
            point sampling; by default, the native engine NAG4M2 is used. Currently, all methods 
            are implemented for reduced and irreducible varieties.
    
	    {\bf Reference:} 
            
            [1] A.J. Sommese and C.W. Wampler, 
            The numerical solution of systems of polynomials.
            {\it World Scientific Publishing} (2005).
///

doc ///
    Key
    	numericalSourceSample
	(numericalSourceSample, Ideal, Thing, ZZ)
        (numericalSourceSample, Ideal, Thing)
	(numericalSourceSample, Ideal, ZZ)
        (numericalSourceSample, Ideal)
    Headline
    	samples a general point on a variety
    Usage
    	numericalSourceSample(I, s)
	numericalSourceSample(I)
    Inputs
	I:Ideal
	    which is prime, specifying a variety $V(I)$
	s:ZZ
	    the number of points to sample on $V(I)$
    Outputs
    	:List
	    of sample points on $V(I)$
    Description
	Text
	    This method computes a list of sample points on a variety numerically. If $I$ is the 
            zero ideal in a polynomial ring of dimension $n$, then an $n$-tuple of random 
            elements in the ground field is returned. Otherwise, a 
            @TO2{numericalIrreducibleDecomposition, "numerical irreducible decomposition"}@ 
            of $I$ is computed, which is then used to sample points.

	    If the number of points $s$ is unspecified, then it is assumed that $s = 1$. 

	    In the example below, we sample a point from $A^3$ and then $3$ points from
	    $V(x^2 + y^2 + z^2 - 1)$ in $A^3$.
            
        Example
            R = CC[x,y,z];
            samp = numericalSourceSample(ideal 0_R)
            samp#0
            I = ideal(x^2 + y^2 + z^2 - 1);
            numericalSourceSample(I, 3)
    Caveat
	Since numerical irreducible decompositions are done over CC, if $I$ is not the zero 
	ideal, then the output will be a point in complex space 
	(regardless of the ground field of the ring of $I$).
    SeeAlso
        numericalImageSample
///

doc ///
    Key
    	numericalImageSample
	(numericalImageSample, Matrix, Ideal, ZZ)
	(numericalImageSample, Matrix, Ideal)
        (numericalImageSample, List, Ideal, ZZ)
	(numericalImageSample, List, Ideal)
        (numericalImageSample, RingMap, Ideal, ZZ)
	(numericalImageSample, RingMap, Ideal)
    Headline
    	samples general points on the image of a variety
    Usage
    	numericalImageSample(F, I, s)
	numericalImageSample(F, I)
    Inputs
    	F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
	I:Ideal
	    which is prime, specifying a source variety $V(I)$
	s:ZZ
	    the number of points to sample in $F(V(I))$
    Outputs
    	:List
	    of sample points on $F(V(I)))$
    Description
	Text
	    This method computes a list of sample points on the image of a variety 
            numerically, by calling @TO numericalSourceSample@.

	    If the number of points $s$ is unspecified, then it is assumed that $s = 1$.

	    The following samples a point from the twisted cubic. We then 
            independently verify that this point does lie on the twisted cubic.
            
        Example
            R = CC[s,t];
            F = {s^3,s^2*t,s*t^2,t^3};
            p = first numericalImageSample(F, ideal 0_R)
            A = matrix{p#Coordinates_{0,1,2}, p#Coordinates_{1,2,3}};
            numericalRank A == 1
    	Text
        
	    Here is how to sample a point from the Grassmannian $Gr(3,5)$ of 
	    $P^2$'s in $P^4$, under its Pl&uuml;cker embedding.
            We take maximal minors of a $3 x 5$ matrix, whose row span
            gives a $P^2$ in $P^4$.
            
        Example
            R = CC[x_(1,1)..x_(3,5)];
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            numericalImageSample(F, ideal 0_R)
    SeeAlso
        numericalSourceSample
///

doc ///
    Key
    	numericalImageDim
	(numericalImageDim, Matrix, Ideal, Point)
	(numericalImageDim, Matrix, Ideal)
        (numericalImageDim, List, Ideal, Point)
	(numericalImageDim, List, Ideal)
        (numericalImageDim, RingMap, Ideal, Point)
	(numericalImageDim, RingMap, Ideal)
    Headline
    	computes the dimension of the image of a variety
    Usage
    	numericalImageDim(F, I, p)
	numericalImageDim(F, I)
    Inputs
    	F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
	I:Ideal
	    which is prime, specifying a source variety $V(I)$
	p:Point
	    a sample point on $V(I)$
    Outputs
    	:ZZ
	    the dimension of $F(V(I)))$
    Description
	Text
	    The method computes the dimension of the image of a variety numerically. 
	    Even if the source variety and map are projective, the affine (= Krull) 
            dimension is returned. This ensures consistency with @TO dim@.

	    The following code computes the affine dimension of the Grassmannian 
            $Gr(3,5)$ of $P^2$'s in $P^4$, under its Pl&uuml;cker embedding.
            
        Example
            R = CC[x_(1,1)..x_(3,5)];
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            numericalImageDim(F, ideal 0_R)
        Text
        
            For comparison, here is how to do the same computation symbolically.
            
        Example
            R = QQ[x_(1,1)..x_(3,5)];
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            dim ker map(R,QQ[y_0..y_(#F-1)],F)
        Text
        
            Next is an example where direct symbolic computation fails to terminate quickly. 
	    Part of the Alexander-Hirschowitz theorem states that the $14$th secant 
	    variety of the $4$th Veronese of $P^4$ has affine dimension $69$, rather than 
	    the expected $14*4 + 13 + 1 = 70$. See J. Alexander, A. Hirschowitz, $Polynomial
            interpolation in several variables$, J. Alg. Geom. 4(2) (1995), 201-222. We 
            numerically verify this below.
            
        Example
            R = CC[a_(1,1)..a_(14,5)];
            F = sum(1..14, i -> basis(4, R, Variables=>toList(a_(i,1)..a_(i,5))));
            time numericalImageDim(F, ideal 0_R)
///

doc ///
    Key
        numericalNullity
        (numericalNullity, Matrix)
        (numericalNullity, Matrix, Boolean)
        (numericalNullity, List, Boolean)
        Precondition
	[numericalHilbertFunction, Precondition]
        [numericalNullity, Precondition]
	SVDGap
	[numericalHilbertFunction, SVDGap]
        [numericalNullity, SVDGap]
    Headline
        computes numerical kernel dimension of a matrix
    Usage
        numericalNullity M
    Inputs
        M:Matrix
            with real or complex entries
    Outputs
        :ZZ
            dimension of the kernel of M
    Description
        Text
            This method computes the dimension of the kernel of a matrix 
            with real or complex entries numerically, via singular value 
            decomposition (see @TO SVD@). 
            
            If $\sigma_1 \ge \ldots \ge \sigma_n$ are the singular values of 
            $M$, then to establish the nullity numerically we look for the 
	    largest "significant" gap between two consecutive singular values, where 
            the gap between $\sigma_i$ and $\sigma_{i+1}$ is "significant" if the ratio 
	    $\sigma_i / \sigma_{i+1}$ exceeds the value of {\tt SVDGap}.
	    If the largest gap is greater than this threshold, then all singular values 
            after the largest gap are considered as numerically zero; if all gaps are 
            less than this threshold, then the matrix is considered numerically full rank.
	    The default value of {\tt SVDGap} is $1e6$.
            
            The option {\tt Precondition} specifies whether the rows of 
	    M will be normalized to have norm $1$ before computing the SVD.
            This helps reveal nullity if the matrix is dense (e.g. for a generic 
            interpolation matrix), but not if the matrix is sparse (e.g. diagonal).
            
        Example
            numericalNullity(matrix{{2, 1}, {0, 1e-5}}, Precondition => false)
            numericalNullity(map(CC^2,CC^2,0))    
    Caveat
        The option {\tt SVDGap} may require tuning by the user.
    SeeAlso
        SVD
        numericalRank
///

doc ///
    Key
    	numericalHilbertFunction
	(numericalHilbertFunction, Matrix, Ideal, List, ZZ)
	(numericalHilbertFunction, Matrix, Ideal, ZZ)
        (numericalHilbertFunction, List, Ideal, List, ZZ)
	(numericalHilbertFunction, List, Ideal, ZZ)
        (numericalHilbertFunction, RingMap, Ideal, List, ZZ)
	(numericalHilbertFunction, RingMap, Ideal, ZZ)
    Headline
    	computes the values of the Hilbert function for the image of a variety
    Usage
    	numericalHilbertFunction(F, I, S, d)
	numericalHilbertFunction(F, I, d)
    Inputs
    	F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
	I:Ideal
	    which is prime, specifying a source variety $V(I)$
	S:List
	    of general points on $F(V(I))$
    	d:ZZ
	    the argument of the Hilbert function of $F(V(I))$
    Outputs
    	:NumericalInterpolationTable
	    containing the number of linearly independent degree $d$ 
            forms in the ideal of the projective closure of $F(V(I))$, 
            along with approximations of those forms
    Description
	Text
	    This method computes values of the Hilbert function of the 
            image of a variety, by numerical interpolation. This technique 
            circumvents the calculation of the kernel of the 
            associated ring map.

            In order to speed up computation, the list $S$ of points 
            can be precomputed (see @TO numericalImageSample@). 
            This list of points can then be re-used in multiple 
            interpolation computations (which can yield a large 
            speedup over performing separate sampling instances, 
            if the ideal $I$ is not the zero ideal).

            In the following, we compute the dimension of the space of 
            quartics in the ideal of the twisted cubic and obtain the expected 
            answer, $22$. Note that one can verify this by dimension counting:
            quartics in the coordinate ring pull back to forms of degree 
            $12$ on $P^1$, of which there is a $13$-dimensional
            space; thus the space of quartics in the 
            defining ideal has dimension $35 - 13 = 22$.
            
        Example
            R = CC[s,t]
            F = basis(3, R)
            numericalHilbertFunction(F, ideal 0_R, 4)
        Text
        
            The following code computes the dimension of Pl&uuml;cker quadrics in 
            the defining ideal of the Grassmannian $Gr(3,5)$ of $P^2$'s in $P^4$.
            
        Example
            R = CC[x_(1,1)..x_(3,5)];
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            S = numericalImageSample(F, ideal 0_R, 60);
            numericalHilbertFunction(F, ideal 0_R, S, 2)
    SeeAlso
    	NumericalInterpolationTable
        extractImageEquations
///

doc ///
    Key
    	NumericalInterpolationTable
        (net, NumericalInterpolationTable)
        hilbertFunctionArgument
        hilbertFunctionValue
        imagePoints
	interpolationBasis
        interpolationSVD
        interpolationMatrix
    Headline
    	the class of all NumericalInterpolationTables
    Description
	Text
    	    This is a type of hash table storing the output of a 
            polynomial interpolation computation, with the following keys: 
        Code
            UL {
                TEX "\\bf hilbertFunctionArgument: the argument, $d$, to the Hilbert function",
                TEX "\\bf hilbertFunctionValue: the value of the Hilbert function at $d$",
                TEX "\\bf imagePoints: a (vertical) list of sample points on the image",
		TEX "\\bf interpolationBasis: a matrix consisting of the degree $d$ monomials",
                TEX "\\bf interpolationSVD: the singular value decomposition of the interpolation matrix",
                TEX "\\bf interpolationMatrix: the matrix obtained by evaluating degree $d$ monomials at the sample points",
		TEX "\\bf map: the map $F$, of which the image is under consideration"
                }
        Example
            R = CC[x_(1,1)..x_(3,5)];
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            T = numericalHilbertFunction(F, ideal 0_R, 2, Verbose => false)
            (T.hilbertFunctionArgument, T.hilbertFunctionValue)
    SeeAlso
    	numericalHilbertFunction
///

doc ///
    Key
    	extractImageEquations
        (extractImageEquations, Matrix, Ideal, ZZ)
        (extractImageEquations, List, Ideal, ZZ)
        (extractImageEquations, RingMap, Ideal, ZZ)
	(extractImageEquations, NumericalInterpolationTable)
        [extractImageEquations, Threshold]
        AttemptExact
        [extractImageEquations, AttemptExact]
    Headline
    	finds implicit equations in a fixed degree for the image of a variety
    Usage
        extractImageEquations(F, I, d)
    	extractImageEquations T
    Inputs
        T:NumericalInterpolationTable
            a numerical interpolation table for $F(V(I))$ of degree $d$
    	F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
	I:Ideal
	    which is prime, specifying a source variety $V(I)$
    	d:ZZ
	    the argument of the Hilbert function of $F(V(I))$
    Outputs
    	:Matrix
	    of implicit degree d equations for $F(V(I))$
    Description
	Text
	    This method finds (approximate) implicit degree $d$ equations for the image 
            of a variety, by @TO2{numericalHilbertFunction, "numerical interpolation"}@. 
            The option {\tt AttemptExact} specifies whether to use the @TO LLL@ algorithm
            to compute "short" equations over $Z$.

	    If a numerical interpolation table has already been computed, then 
            to avoid repetitive calculation one may run this function with the interpolation 
            table as input.

            For example, we determine the defining quadrics of the twisted cubic, as follows.
            
        Example
            R = CC[s,t]
            F = basis(3, R)
            extractImageEquations(F, ideal 0_R, 2, AttemptExact => true)
        Text
        
            Here is how to do the same computation symbolically.
            
        Example
            transpose gens ker map(QQ[s,t], QQ[y_0..y_3], {s^3,s^2*t,s*t^2,t^3})
        Text
        
	    We determine the $5$ Pl&uuml;cker quadrics defining the Grassmannian 
            $Gr(3,5)$.
            
        Example
            R = CC[x_(1,1)..x_(3,5)]; I = ideal 0_R;
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
	    T = numericalHilbertFunction(F, I, 2, Verbose => false);
	    extractImageEquations(T, AttemptExact => true)
        Text
        
    	    The option {\tt Threshold} sets the threshold for rounding the interpolation matrix. 
            If this option has value $n$, then the interpolation matrix will be rounded
            to $n$ decimal digits, after which LLL will be performed. The default value is $8$.
    SeeAlso
    	numericalHilbertFunction
        NumericalInterpolationTable
///

doc ///
    Key
    	numericalImageDegree
	(numericalImageDegree, Matrix, List, List, Thing)
        (numericalImageDegree, Matrix, Ideal)
	(numericalImageDegree, Matrix, Ideal, Point)
	(numericalImageDegree, Matrix, Ideal, List, Thing)
        (numericalImageDegree, Matrix, Ideal, Point, Thing)
        (numericalImageDegree, List, List, List, Thing)
        (numericalImageDegree, List, Ideal)
	(numericalImageDegree, List, Ideal, Point)
	(numericalImageDegree, List, Ideal, List, Thing)
        (numericalImageDegree, List, Ideal, Point, Thing)
        (numericalImageDegree, RingMap, List, List, Thing)
        (numericalImageDegree, RingMap, Ideal)
	(numericalImageDegree, RingMap, Ideal, Point)
	(numericalImageDegree, RingMap, Ideal, List, Thing)
        (numericalImageDegree, RingMap, Ideal, Point, Thing)
        Repeats
    	[numericalImageDegree, Repeats]
        MaxAttempts
    	[numericalImageDegree, MaxAttempts]
        MaxPoints
    	[numericalImageDegree, MaxPoints]
        DoRefinements
        [numericalImageDegree, DoRefinements]
	DoTraceTest
	[numericalImageDegree, DoTraceTest]
        TraceThreshold
    	[numericalImageDegree, TraceThreshold]
    	[numericalImageDegree, Threshold]
        [isOnImage, Threshold]
    Headline
    	computes a pseudo-witness set for the image of a variety
    Usage
    	numericalImageDegree(F, I, p)
	numericalImageDegree(F, I)
    Inputs
    	F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
	I:Ideal
	    which is prime, specifying a source variety $V(I)$
	p:Point
	    a general point on $V(I)$
    Outputs
    	:PseudoWitnessSet
	    containing the degree of the projective closure of $F(V(I))$, 
            along with a pseudo-witness set for $F(V(I))$
    Description
	Text
	    This method computes the degree of the image of a variety, 
            along with a @TO2{PseudoWitnessSet, "pseudo-witness set"}@
            for it, by computing the intersection of the image with a 
	    complementary-dimensional linear slice via tracking monodromy loops 
	    with homotopy continuation, and then applying the trace test. If 
	    the trace test fails, only a lower bound for the degree and an 
	    incomplete pseudo-witness set is returned. This technique circumvents 
	    the calculation of the kernel of the associated ring map.
	    
	    The method also allows the user to provide a particular linear slice $L$ of the 
	    image. In this case a list of point pairs $(p, q)$ such that $p$ is in $V(I)$,
	    $q = F(p)$, and $q$ is in $L$. The method then applies monodromy to try to 
	    compute the entire intersection $F(X) \cap $ $L$. If no linear slice is given,
	    then a random complementary-dimensional linear slice will be chosen.

            The following code computes the degree of the Grassmannian 
            $Gr(3,5)$ of $P^2$'s in $P^4$.
            
        Example
            R = CC[x_(1,1)..x_(3,5)];
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            W = numericalImageDegree(F, ideal 0_R)
            W.isCompletePseudoWitnessSet
            W.degree
        Text
        
            This method can also handle cases where the parameterization 
            has positive dimensional fibers. In the example below, we verify that 
            the variety of $3 x 3 x 3$ tensors of border rank $<= 4$, i.e. the $4$th secant 
            variety of $P^2 x P^2 x P^2$, has degree $9$. This is a hypersurface, 
            with defining equation known as Strassen's invariant,
            and it is also a defective secant variety (meaning its dimension is less
            than expected). Here, the parametrization has $10$ dimensional fibers.
	    For more on this example, see V. Strassen, $The asymptotic spectrum of tensors$, 
	    J. Reine Angew. Math. 384 (1988), 102-152.
            
        CannedExample
            i6 : R = CC[a_(0,0)..a_(3,2), b_(0,0)..b_(3,2), c_(0,0)..c_(3,2)];
            
            i7 : F = toList apply((0,0,0)..(2,2,2), (i,j,k) ->
                    a_(0,i)*b_(0,j)*c_(0,k) +
                    a_(1,i)*b_(1,j)*c_(1,k) +
                    a_(2,i)*b_(2,j)*c_(2,k) +
                    a_(3,i)*b_(3,j)*c_(3,k));
                    
            i8 : numericalImageDegree(F, ideal 0_R, Repeats => 2)
            Sampling point in source ...
            Tracking monodromy loops ...
            Points found: 1
            Points found: 2
            Points found: 3
            Points found: 5
            Points found: 7
            Points found: 9
            Points found: 9
            Points found: 9
            Running trace test ...
            
            o8 = a pseudo-witness set, indicating
                the degree of the image is 9
            
            o8 : PseudoWitnessSet
        Text
        
            Finally, this method has a large number of optional inputs which may be 
            specified by the user to fit a particular problem instance. 

    	    The option {\tt Repeats} sets the maximum number of consecutive repetitive 
            monodromy loops when computing a pseudo-witness set. A repetitive 
            monodromy loop is one where no new points in the image are discovered. 
            After this many consecutive repetitive monodromy loops occur, the trace 
            test is applied to determine if a complete pseudo-witness set has 
            been found. The default value is $3$.

    	    The option {\tt MaxAttempts} sets the maximum number of times the trace test 
            will be attempted when computing a pseudo-witness set. After a trace test 
            fails, a new slice is chosen, the previous points are tracked to the new 
            slice, and monodromy is performed anew. If the trace test has failed 
            {\tt MaxAttempts} many times, an incomplete pseudo-witness set is returned. 
            The default value is $10$.
            
            Here is an example in which a badly chosen random seed results in a 
            failed trace test on the first attempt.  In later attempts, the trace test 
            passes and the degree of the twisted cubic is correctly computed to be $3$.
            
        Example
            setRandomSeed 10
            R = CC[s,t]
            F = basis(3, R)
            numericalImageDegree(F, ideal 0_R)
        Text
        
            We compare this with the native $Macaulay2$ function {\tt degree} (using
            symbolic computation).
            
        Example
            degree ker map(QQ[s,t], QQ[y_0..y_3], {s^3,s^2*t,s*t^2,t^3})
        Text
            
            The option {\tt MaxPoints} sets a number of points such that if more than this 
	    number of points is found following a monodromy loop, then the method gracefully 
	    exits. The option is especially useful in the case that the user specifies a 
	    linear slice $L$ (as discussed above) which is in special position with respect to 
	    $F(V(I))$ (e.g. if $F(V(I)) \cap L$ is positive-dimensional). The default value 
	    is @TO infinity@.
            
            The option {\tt DoRefinements} specifies whether or not to refine solution points found 
            via monodromy.
	    
	    The option {\tt DoTraceTest} specifies whether or not to run the trace test.
            
    	    The option {\tt TraceThreshold} sets the threshold for a pseudo-witness set to pass 
            the trace test. The trace for a complete exact pseudo-witness set is 
            $0$; large nonzero values indicate failure (the larger the value, the worse 
            the failure). The default value is $1e-5$. Caution: setting the value of this 
            threshold too high may result in the trace test returning false positives.

    	    The option {\tt Threshold} sets the threshold for determing point equality. 
            If this option has value $n$, then two points are considered equal iff their 
            first $n$ significant digits agree (equivalently, in scientific notation, the 
            exponents and first $n$ digits of the mantissa agree). The default value is $5$. 
    SeeAlso
    	PseudoWitnessSet
///

doc ///
    Key
        PseudoWitnessSet
        (net, PseudoWitnessSet)
        isCompletePseudoWitnessSet
	sourceEquations
        sourceSlice
        generalCombinations
        imageSlice
        witnessPointPairs
    Headline
    	the class of all pseudo-witness sets
    Description
	Text
            This is a type of hash table storing the output of a 
            pseudo-witness set computation using monodromy, 
            with the following keys:
        Code
            UL {
                {TEX "\\bf isCompletePseudoWitnessSet: whether the pseudo-witness set has passed the trace test, according to the trace test threshold"},
                TEX "\\bf degree: the number of image points found by monodromy",
                TEX "\\bf map: the map $F$, of which the image is under consideration",
                TEX "\\bf sourceEquations: the defining ideal $I$ of the source variety",
                {TEX "\\bf sourceSlice: additional equations to form a zero-dimensional system (only needed if the map is not finite-to-one)"},
                {TEX "\\bf generalCombinations: additional equations to form a zero-dimensional system (only needed if the source ideal is not a complete intersection)"},
                TEX "\\bf imageSlice: a general complementary-dimensional linear space to $F(V(I))$",
                {TEX "\\bf witnessPointPairs: a vertical list of 2-point sequences $(p, F(p))$, where $p$ lies on $V(I)$ and $F(p)$ lies on imageSlice"},
                {TEX "\\bf witnessSet: a witness set for $V(I)$ (only computed if $I$ is not the zero ideal)"}, 
                TEX "\\bf trace: the result of the trace test applied to witnessPointPairs"
                }
        Text
	    For a discussion of pseudo-witness sets, 
	    see J. D. Hauenstein and A. J. Sommese, $Witness sets of projections$, 
	    Appl. Math. Comput. 217(7) (2010), 3349-3354. 
	    
	    The following example demonstrates the output for the 
            degree $3$ embedding of $P^1$ into $P^3$, whose image is the twisted cubic.
            
	Example
            R = CC[s,t];
            W = numericalImageDegree(basis(3,R), ideal 0_R, Verbose => false);
            peek W
    SeeAlso
    	numericalImageDegree
///

doc ///
    Key
    	traceTest
	(traceTest, Matrix, ZZ, List, List)
    Headline
    	performs the trace test
    Usage
	traceTest(F, d, S, L)
    Inputs
        F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
        d:ZZ
            the dimension of a linear slice
        S:List
            of point pairs (p, q) with q = F(p)
	L:List
	    start system
    Outputs
    	:Boolean
	    whether the point $p$ lies on $F(V(I))$
    Description
	Text
	    This method determines if a point in the ambient target space 
            lies on the image of a variety. This is done via computing a 
            pseudo-witness set for the image.

            If a pseudo-witness set has already been computed, then 
            to avoid repetitive calculation one may run this function with the 
            pseudo-witness set as input.

            The following determines whether a point lies on the
            Grassmannian $Gr(3,5)$ of $P^2$'s in $P^4$.
            
        Example
            R = CC[x_(1,1)..x_(3,5)]; I = ideal 0_R;
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            W = numericalImageDegree(F, I, Repeats => 2, Verbose => false);
            q = first numericalImageSample(F, I)
            isOnImage(W, q)
            isOnImage(W, point random(CC^1, CC^#F))
            isOnImage(W, point{{1_CC,0,0,0,0,0,0,0,0,0}})
    SeeAlso
    	PseudoWitnessSet
        numericalImageDegree
///

doc ///
    Key
    	isOnImage
	(isOnImage, PseudoWitnessSet, Point)
	(isOnImage, Matrix, Ideal, Point)
        (isOnImage, List, Ideal, Point)
        (isOnImage, RingMap, Ideal, Point)
    Headline
    	tests whether a point lies on the image of a variety
    Usage
    	isOnImage(W, p)
	isOnImage(F, I, p)
    Inputs
        W:PseudoWitnessSet
            a pseudo-witness set for $F(V(I))$
	p:Point
	    a point in the ambient space of $F(V(I))$
        F:
	    a @TO2{Matrix, "matrix"}@, or @TO2{List, "list"}@, or 
	    @TO2{RingMap, "ring map"}@, specifying a map
	I:Ideal
	    which is prime, specifying a source variety $V(I)$
    Outputs
    	:Boolean
	    whether the point $p$ lies on $F(V(I))$
    Description
	Text
	    This method determines if a point in the ambient target space 
            lies on the image of a variety. This is done via computing a 
            pseudo-witness set for the image.

            If a pseudo-witness set has already been computed, then 
            to avoid repetitive calculation one may run this function with the 
            pseudo-witness set as input.

            The following determines whether a point lies on the
            Grassmannian $Gr(3,5)$ of $P^2$'s in $P^4$.
            
        Example
            R = CC[x_(1,1)..x_(3,5)]; I = ideal 0_R;
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            W = numericalImageDegree(F, I, Repeats => 2, Verbose => false);
            q = first numericalImageSample(F, I)
            isOnImage(W, q)
            isOnImage(W, point random(CC^1, CC^#F))
            isOnImage(W, point{{1_CC,0,0,0,0,0,0,0,0,0}})
    SeeAlso
    	PseudoWitnessSet
        numericalImageDegree
///

doc ///
    Key
        [numericalHilbertFunction, Verbose]
    	[numericalImageDegree, Verbose]
	[isOnImage, Verbose]
        [numericalNullity, Verbose]
    Headline
    	display detailed output
    Usage
        numericalImageDegree(..., Verbose => true)
	numericalHilbertFunction(..., Verbose => true)
	isOnImage(..., Verbose => true)
        numericalNullity..., Verbose => true)
    Description
	Text
    	    This option determines whether detailed output is displayed 
            during an interpolation or monodromy computation, 
            including timings for various intermediate computations. 
            The default value is true.
    SeeAlso
        numericalHilbertFunction
    	numericalImageDegree
	isOnImage
///

doc ///
    Key
        IsGraded
	[numericalImageSample, IsGraded]
	[numericalImageDim, IsGraded]
        [numericalHilbertFunction, IsGraded]
        [numericalImageDegree, IsGraded]
        [isOnImage, IsGraded]
    Headline
        specifies whether input is homogeneous
    Usage
        numericalHilbertFunction(..., IsGraded => true)
        numericalImageDegree(..., IsGraded => true)
        isOnImage(..., IsGraded => true)
    Description
        Text
            This option specifies whether input (i.e. the ideal $I$ and map $F$)
            is graded. If false, input will be homogenized with respect 
            to a new variable, and internally the target variety is treated
            as the affine cone over its projective closure. The default value is true.
    SeeAlso
    	numericalImageSample
	numericalImageDim
        numericalHilbertFunction
        numericalImageDegree
        isOnImage
///

doc ///
    Key
        MaxThreads
    	[numericalImageDegree, MaxThreads]
        [isOnImage, MaxThreads]
    Headline
    	specifies the maximum number of processor threads
    Usage
        numericalImageDegree(..., MaxThreads => allowableThreads)
    Description
	Text
    	    This option sets the maximum number of processor threads that will be used 
            for parallel computation. This distributes the paths to track in each 
            monodromy loop among the processors as evenly as possible. 
            The value of this option should never exceed the value of the variable 
            @TO allowableThreads@. The default value of {\tt MaxThreads} is $1$.
    Caveat
        Parallel computation in $Macaulay2$ is under development. Unexpected errors 
        may be printed to output while computing a pseudo-witness set - however, the 
        loop will still run, and an answer will still be returned.
        
        If the number of paths to track is too low (i.e. ≤ $20$), parallel computing will 
        not be used.
    SeeAlso
    	numericalImageDegree
///

doc ///
    Key
        [numericalImageDegree, Software]
	[numericalSourceSample, Software]
        [numericalImageSample, Software]
        [numericalImageDim, Software]
        [numericalHilbertFunction, Software]
        [isOnImage, Software]
    Headline
    	specify software for homotopy continuation
    Usage
        numericalImageDegree(..., Software => M2engine)
        numericalImageSample(..., Software => M2engine)
        numericalImageDim(..., Software => M2engine)
        numericalHilbertFunction(..., Software => M2engine)
        isOnImage(..., Software => M2engine)
    Description
	Text
    	    This option specifies the software used for polynomial homotopy 
            continuation (used for path tracking) and numerical irreducible 
            decompositions (used for sampling points). The default value is 
            M2engine (native to $Macaulay2$). Other possible values are 
            @TO Bertini@ and @TO PHCpack@ (only if the user has these 
            packages installed).
    SeeAlso
        numericalImageDegree
	numericalSourceSample
        numericalImageSample
        numericalImageDim
        numericalHilbertFunction
        isOnImage
///

undocumented {
    numericalEval,
    (numericalEval, Matrix, List, Boolean),
    (isWellDefined, PseudoWitnessSet),
    (isWellDefined, NumericalInterpolationTable)
}


TEST /// -- embedding cubic surface (with 3 singular points) in P^3 via 5 sections of O(2)
setRandomSeed 0
d = dim ker map(QQ[x,y,z,w]/ideal(x^3 - y*z*w), QQ[a_0..a_4], {x*w + 2*x*y, x*w-3*y^2, z^2, x^2 + y^2 + z^2 - w^2, 3*y*w - 2*x^2})
R = CC[x,y,z,w]
I = ideal(x^3 - y*z*w)
F = {x*w + 2*x*y, x*w-3*y^2, z^2, x^2 + y^2 + z^2 - w^2, 3*y*w - 2*x^2}
assert(numericalImageDim(F, I) == d)
-- Cf. also: non-homogeneous ideal (x^5 - y*z*w), kernel over finite fields
///

TEST /// -- twisted cubic
setRandomSeed 0
R = CC[s,t]
F = basis(3,R)
J = monomialCurveIdeal(QQ[a_0..a_3], {1,2,3})
assert(all(1..5, d -> (numericalHilbertFunction(F,ideal 0_R,d)).hilbertFunctionValue == numcols super basis(d,J)))
W = numericalImageDegree(F, ideal 0_R);
assert(W.degree == 3)
assert(isOnImage(W, first numericalImageSample(F,ideal 0_R)) == true)
assert(isOnImage(W, point random(CC^1,CC^(numcols F))) == false)
///

TEST /// -- Rational quartic curve in P^3
setRandomSeed 0
R = CC[s,t]
F = flatten entries basis(4, R) - set{s^2*t^2}
S = QQ[a_0..a_3]
I3 = super basis(3, ker map(QQ[s,t], S, {s^4,s^3*t,s*t^3,t^4}))
T = numericalHilbertFunction(F, ideal 0_R, 3);
M = extractImageEquations(T, AttemptExact => true)
assert(image transpose M == image (map(ring M, S, gens ring M))(I3))
///

TEST /// -- Grassmannian Gr(3, 5) = G(2,4)
setRandomSeed 0
(k, n) = (3,5)
R = CC[x_(1,1)..x_(k,n)]
I = ideal 0_R
F = (minors(k, genericMatrix(R, k, n)))_*
assert(numericalImageDim(F, I) == 1 + k*(n-k))
T = numericalHilbertFunction(F, I, 2)
J = super basis(2, Grassmannian(k-1,n-1))
assert(T.hilbertFunctionValue == numcols J)
I2 = image transpose extractImageEquations(T, AttemptExact => true)
assert(image (map(ring I2, ring J, gens ring I2))(J) == I2)
time W = numericalImageDegree(F, I, Repeats => 2, Verbose => false)
assert(W.degree == 5)
(n, m) = (5, 10)
pointList = numericalImageSample(F, I, n);
assert(all(pointList, q -> (tally apply(m, i -> isOnImage(W, q)))#true / m >= 8/10))
///

TEST /// -- random canonical curve of genus 4, under random projection to P^2 by cubics
setRandomSeed 0
R = CC[x_0..x_3]
I = ideal(random(2,R),random(3,R))
F = toList(1..3)/(i -> random(3,R))
assert((numericalImageDegree(F,I)).degree == 18)
S = numericalImageSample(F,I,190);
assert((numericalHilbertFunction(F,I,S,18)).hilbertFunctionValue == 1)
///

TEST /// -- Segre + Veronese
setRandomSeed 0
-- Veronese surface P^2 in P^5
(d, n) = (2, 2)
R = CC[x_0..x_n]
F = basis(d, R)
PW = numericalImageDegree(F, ideal 0_R)
assert(PW.degree == 4)
assert((numericalImageDegree(PW.map, PW.sourceEquations, PW.witnessPointPairs_{1}, PW.imageSlice)).degree == 4)
assert((numericalImageDegree(PW.map, PW.sourceEquations, PW.witnessPointPairs_{0,2}, PW.imageSlice)).degree == 4)
I2 = ideal extractImageEquations(F, ideal 0_R, 2, AttemptExact => true)
S = QQ[y_0..y_(binomial(d+n,d)-1)]
RQ = QQ[x_0..x_n]
J = ker map(RQ, S, basis(d, RQ))
assert((map(ring I2, S, gens ring I2))(J) == I2)
-- Segre P^2 x P^3
(n1, n2) = (2, 4)
R = CC[s_0..s_(n1), t_0..t_(n2)]
F = (ideal(s_0..s_(n1))*ideal(t_0..t_(n2)))_*
I2 = ideal extractImageEquations(F, ideal 0_R, 2, AttemptExact => true)
RQ = QQ[s_0..s_(n1), t_0..t_(n2)]
S = QQ[y_0..y_((n1+1)*(n2+1)-1)]
J = ker map(RQ, S, (ideal(s_0..s_(n1))*ideal(t_0..t_(n2)))_*)
assert((map(ring I2, S, gens ring I2))(J) == I2)
///

TEST /// -- Iterated Veronese
(d1,d2) = (2,3)
R = CC[x_0..x_(d1)]
I = ideal(x_0*x_2 - x_1^2)
W = first components numericalIrreducibleDecomposition I
S = CC[y_0..y_(binomial(d1+d2,d2)-1)]
F = map(R,S,basis(d2,R))
eps = 1e-10
p1 = first numericalSourceSample(I)
assert(clean(eps, sub(gens I, matrix p1)) == 0)
p2 = first numericalSourceSample(I, W)
assert(clean(eps, sub(gens I, matrix p2)) == 0)
P = numericalSourceSample(I, W, 10)
assert(all(P/matrix, p -> clean(eps, sub(gens I, p)) == 0))
q1 = numericalImageSample(F, I)
Q = numericalImageSample(F, I, 10)
S = numericalImageSample(F,I,55)
T = numericalHilbertFunction(F,I,S,2)
assert(T.hilbertFunctionValue == 42)
assert(isWellDefined T)
PW = numericalImageDegree(F, I, p1)
assert(isWellDefined PW)
assert(PW.degree == 6)
assert((numericalImageDegree(F, I)).degree == 6)
assert((numericalImageDegree(F, I, PW.witnessPointPairs#0#0, PW.imageSlice)).degree == 6)
assert((numericalImageDegree(F, I, PW.witnessPointPairs, PW.imageSlice)).degree == 6)
assert((numericalImageDegree(F, {I, W}, PW.witnessPointPairs, PW.imageSlice)).degree == 6)
///

TEST /// -- SO(n)
setRandomSeed 0
n = 4
R = CC[x_(1,1)..x_(n,n)]
A = genericMatrix(R,n,n)
I = ideal(A*transpose A - id_(R^n)) + ideal(det A - 1);
p = point{flatten entries id_(CC^n)}
F = vars R
assert(numericalImageDim(F,I,p) === n*(n-1)//2)
assert((numericalImageDegree(F,I,p, Repeats=>2, TraceThreshold => 1e-3, Threshold => 2)).degree == 2^(n-1)*det matrix apply(toList(1..floor(n/2)), i -> apply(toList(1..floor(n/2)), j -> binomial(2*n - 2*i - 2*j, n - 2*i))))
///

TEST /// -- Twisted cubic projections
R = CC[x_0..x_3]
I = monomialCurveIdeal(R, {1,2,3})
F1 = random(R^1, R^{3:-1})
p = numericalSourceSample I
imagePts = numericalImageSample(F1, I, 10);
assert(numericalImageDim(F1, I, p#0) == 2)
assert((numericalHilbertFunction(F1, I, imagePts, 2, Verbose=>false)).hilbertFunctionValue == 0)
assert((numericalHilbertFunction(F1, I, imagePts, 3, Verbose=>false)).hilbertFunctionValue == 1)
F2 = (gens R)_{0,2,3}
T = numericalHilbertFunction(F2, I, 3)
nodalCubic = extractImageEquations(T, AttemptExact => true)
S = ring nodalCubic
assert(ideal nodalCubic == ideal(S_1^3 - S_0*S_2^2))
F3 = (gens R)_{0,1,2}
assert((numericalHilbertFunction(F3, I, 2, Verbose=>false)).hilbertFunctionValue == 1)
PW = numericalImageDegree(F2, I, p#0)
assert(PW.degree == 3)
///

TEST ///
assert(numericalNullity(matrix{{2, 1}, {0, 1e-7}}, Precondition => false) == 1)
assert(numericalNullity(map(CC^2,CC^2,0)) == 2)
assert(numericalNullity(id_(CC^2)) == 0)
assert(numericalNullity(random(CC^2,CC^2)) == 0)
///

end--

restart
needsPackage "NumericalImplicitization"
loadPackage("NumericalImplicitization", Reload => true)
uninstallPackage "NumericalImplicitization"
installPackage "NumericalImplicitization"
installPackage("NumericalImplicitization", RemakeAllDocumentation => true)
viewHelp "NumericalImplicitization"
check "NumericalImplicitization"



-- Magic numbers: 8 decimal places in extractImageEquations, 10 in fiberSlice, 20 in myTrack (for parallelization), 4 (translationMagnitude) in traceTest

-- Future:
-- Faster evaluation at multiple points (multivariate Horner / SLP?)


-- high degree rational normal curve
R = CC[s,t],; F = basis(40,R); I = ideal 0_R;
numericalImageDim(F, I)
time tests = toList(1..100)/(i -> numericalImageDegree(F,I,Repeats=>2,Verbose=>false));


-- Generic Pinched Veronese
R = CC[x_0..x_3]
F = toList(1..5)/(i -> random(10,R));
allowableThreads = maxAllowableThreads
numericalImageDegree(F,ideal 0_R,Repeats=>2)


-- Trifocal variety
R=CC[a00,a01,a02,a03,a10,a11,a12,a13,a20,a21,a22,a23,b10,b11,b12,b13,b20,b21,b22,b23],;A = transpose genericMatrix(R,a00,4,3),;B = matrix{{0,0,0,1},{b10,b11,b12,b13},{b20,b21,b22,b23}},;C = matrix{{1_R,0,0,0},{0,1,0,0},{0,0,1,0}},;M = A||B||C,;F = flatten flatten apply(3, i-> apply(3, j-> apply(reverse subsets(3,2), k->det  submatrix(M,{i}|{j+3}|(k+{6,6}) , )  )   ));
allowableThreads = 4
elapsedTime numericalImageDegree(F,ideal 0_R,Repeats=>2,MaxThreads=>allowableThreads)


-- Tensor product surface
(a,b) = (3,1)
R=CC[s,t,u,v, Degrees=>{{1,0},{1,0},{0,1},{0,1}}]
Ix=intersect(ideal(s,u),ideal(t,v))
B=super basis({a,b},Ix)
C=matrix{{1_R,1,0,0,0,0},{0,1,1,0,0,0},{0,0,1,1,0,0},{0,0,0,1,1,1}}
F = C*transpose(B)
I = ideal 0_R
numericalImageDim(F,I)
W = numericalImageDegree(F,I)
T = numericalHilbertFunction(F,I,W.degree)
extractImageEquations(T, AttemptExact => true)


-- Undirected graphical model on 4 variables
setRandomSeed 0
loadPackage "GraphicalModels"
G = graph({1,2,3,4},{{1,2},{1,3},{2,3},{3,4}})
R = CC[x_(1,1),x_(1,2),x_(1,4),x_(2,2),x_(2,4),x_(3,3),x_(3,4),x_(4,4)]
M = matrix{{x_(1,1),x_(1,2),0,x_(1,4)},{x_(1,2),x_(2,2),0,x_(2,4)},{0,0,x_(3,3),x_(3,4)},{x_(1,4),x_(2,4),x_(3,4),x_(4,4)}}
F = flatten(for i from 1 to 4 list (
    for j from i to 4 list (
	det(submatrix'(M, {i-1}, {j-1}))
    )
))
I = ideal 0_R
numericalImageDim(F, I)
numericalImageDegree(F, I, Repeats => 2)
T = numericalHilbertFunction(F, I, 2)
extractImageEquations(T, AttemptExact => true)


-- Check approximate equations:
T = numericalHilbertFunction(F, ideal 0_R, 2);
E = extractImageEquations(T, AttemptExact => true);
all((toList T.imagePoints)/(p -> clean(1e-11, sub(E, toList(0..<#(p#Coordinates))/(i -> (gens ring E)#i => (p#Coordinates)#i)))), v -> v == 0)


--------------- Implicitization Challenge + variants

-- (line) secant of (P^1)^n, n = 5: degree 3256
n = 5
R = CC[a_1..a_n,b_1..b_n,s,t];
F = s*(terms product apply(toList(1..n), i->(1 + a_i))) + t*(terms product apply(toList(1..n), i->(1 + b_i)));
allowableThreads = maxAllowableThreads
time W = numericalImageDegree(F, ideal 0_R, Repeats => 1, MaxThreads => allowableThreads) 


-- Challenge: Hadamard square of line secant of (P^1)^4, degree 110, passed in 188.084 seconds
t = symbol t;
n = 4
R = CC[a_1..a_n,b_1..b_n, c_1..c_n, d_1..d_n,t_0..t_3];
F1 = t_0*(terms product apply(toList(1..n), i->(1 + a_i))) + t_1*(terms product apply(toList(1..n), i->(1 + b_i)));
F2 = t_2*(terms product apply(toList(1..n), i->(1 + c_i))) + t_3*(terms product apply(toList(1..n), i->(1 + d_i)));
F = apply(toList(0..15), i -> F1#i * F2#i);
allowableThreads = maxAllowableThreads
time W = numericalImageDegree(F, ideal 0_R, Repeats => 1, MaxThreads => allowableThreads)


-- precision tests

R = CC_54[s,t]; I = ideal 0_R; W = numericalImageDegree(basis(3, R), I)
toList W.witnessPointPairs /first/(p -> p#Coordinates )/first/ring

prec = 500
setDefault(Precision => prec)
R = CC_prec[s,t]; I = ideal 0_R; F = basis(3, R);
W = numericalImageDegree(F, I)

R = CC[s,t]; F = basis(4, R); I = ideal 0_R
T = numericalHilbertFunction(F, I, 2)
A = matrix T.interpolationMatrix

prec = 5
printingPrecision = 16
setDefault(Precision => prec)
R = CC_prec[x_0..x_3]
R = CC[x_0..x_2]
I = ideal random(R^1,R^{-2,-3})
I = ideal(random(2,R), random(3,R))
F = random(R^1,R^{3:-3})
F = matrix{toList(1..3)/(i -> random(3,R))}
d = 18


-- Dim example
jacI=(d,l,n)->(S=CC[x_(0,1)..x_(n,l),c_0..c_(binomial(l,n)-1)];R= S[X_0..X_n];
M=for i from 1 to l list matrix{toList (x_(0,i)..x_(n,i))};
H=for b in(for i from 0 to#subsets(M,n)-1 list for a in(subsets(M,n))_i list{a})
list matrix b;
P=for t from 0 to #H-1 list for j from 0 to n list(-1)^(j)*(minors(n,H_t))_(n-j);
F=sum for i from 0 to #P-1 list c_(i)*(sum for j from 0 to n list P_i_j*X_j)^d;
I=transpose substitute((coefficients F)#1,S))

t=13
time F = jacI(t,t+1,2);
time F = value first lines get "jac13.txt";
time numericalImageDim(F, ideal 0_S)
