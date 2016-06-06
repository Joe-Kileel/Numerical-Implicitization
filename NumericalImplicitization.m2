newPackage("NumericalImplicitization",
    Headline => "NumericalImplicitization",
    Version => "1.0",
    Date => "June 5, 2016",
    Authors => {
        {Name => "Justin Chen",
	 Email => "jchen@math.berkeley.edu"},
        {Name => "Joe Kileel",
	 Email => "jkileel@math.berkeley.edu",
	 HomePage => "http://www.math.berkeley.edu/~jkileel"}
        },
    PackageImports => {},
    PackageExports => {"NumericalAlgebraicGeometry"},
    DebuggingMode => true
    )
    export {
        "numericalImageSample",
        "numericalImageDim",
        "numericalHilbertFunction",
	    "numericalInterpolationTable",
            "SVDGapThreshold",
            "verboseOutput",
            "hilbertFunctionArgument",
            "hilbertFunctionValue",
            "numericalImageEquations",
            "imagePoints",
            "interpolationSVD",
	"numericalImageDegree",
	    "pseudoWitnessSet",
            "traceTestThreshold",
            "maxMonodromyLoops",
            "maxTraceTests",
            "isCompletePseudoWitnessSet",
            "imageDegreeLowerBound",
            "sourceSlice",
            "imageSlice",
            "witnessPointPairs",
	"isOnImage"
    }

debug NumericalAlgebraicGeometry

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

numericalInterpolationTable = new Type of HashTable
globalAssignment numericalInterpolationTable
net numericalInterpolationTable := X -> (
	if hasAttribute(X, ReverseDictionary) then toString getAttribute(X, ReverseDictionary)
	else "numericalInterpolationTable"
)

pseudoWitnessSet = new Type of HashTable
globalAssignment pseudoWitnessSet
net pseudoWitnessSet := X -> (
	if hasAttribute(X, ReverseDictionary) then toString getAttribute(X, ReverseDictionary)
	else "pseudoWitnessSet"
)

--software options for numericalIrreducibleDecomposition and track
--default is M2engine throughout
--none for sample nor refine
--n.b.: precision loss from LAPACK in SVD computation
--add verboseOutput options to numericalImageDegree and isOnImage

smartSample = method(Options => {Software => M2engine})
smartSample (Ideal, ZZ) := List => opts -> (I, sampleSize) -> ( --outputs a list of random sample points of V(I)
    if I == 0 then toList(1..sampleSize)/(i -> point{apply(gens(ring(I)), x -> random coefficientRing(ring(I)))})
    else smartSample(I, first components(numericalIrreducibleDecomposition(I, opts)), sampleSize)
)
smartSample (Ideal, WitnessSet, ZZ) := List => opts -> (I, W, sampleSize) -> (
    samplePoints := toList(1..sampleSize)/(i -> sample(W));
    if precision(ring(I)) <= precision(ring(first (first samplePoints)#Coordinates)) then return samplePoints;
    refine(polySystem(I_*), samplePoints, Bits => precision(ring(I)))
)
smartSample (Ideal) := Point => opts -> (I) -> first smartSample(I, 1, opts)
smartSample (Ideal, WitnessSet) := Point => opts -> (I, W) -> first smartSample(I, W, 1, opts)

    
numericalImageSample = method(Options => {Software => M2engine})
numericalImageSample (List, Ideal, ZZ) := List => opts -> (F, I, sampleSize) -> (
    apply(smartEval(F, smartSample(I, sampleSize, opts), false), p -> point p)
)
numericalImageSample (List, Ideal) := Point => opts -> (F, I) -> first numericalImageSample(F, I, 1, opts)


numericalDims = method(Options => {Software => M2engine})
numericalDims (List, Ideal, Point) := List => opts -> (F, I, sourcePoint) -> ( --outputs {dim(V(I)), dim(F(V(I))}
    m := #F;
    n := #gens(ring(I));
    C := coefficientRing(ring(I));
    sourceJacobian := sub(transpose(jacobian(I)), matrix sourcePoint);
    k := numrows(sourceJacobian); --equals numcols(gens(I))
    dF := sub(transpose(jacobian(matrix{F})), matrix sourcePoint);
    sourceDim := smartNullity(sourceJacobian, false);
    {sourceDim, sourceDim - smartNullity(sourceJacobian || -dF, false)}
)
numericalDims (List, Ideal) := ZZ => opts -> (F, I) -> numericalDims(F, I, smartSample(I, opts))


numericalImageDim = method(Options => {Software => M2engine})
numericalImageDim (List, Ideal, Point) := ZZ => opts -> (F, I, sourcePoint) -> last numericalDims(F, I, sourcePoint, opts)
numericalImageDim (List, Ideal) := ZZ => opts -> (F, I) -> last numericalDims(F, I, opts)


smartNullity = method(Options => {symbol SVDGapThreshold => 200, symbol verboseOutput => false})
smartNullity (Matrix, Boolean) := List => opts -> (M, keepSVD) -> (
    if opts.verboseOutput then (
	print "Performing normalization preconditioning ...";
	time normalizedM := matrix apply(entries M, row -> if matrix{row} == 0 then row else (1/norm(2,row))*row);
	print "Computing numerical kernel ...";
	if M == 0 then return if keepSVD then {numcols M, 0} else numcols M;
	time (S, U, Vt) := SVD(normalizedM, DivideConquer => true);
    ) else (
        normalizedM = matrix apply(entries M, row -> if matrix{row} == 0 then row else (1/norm(2,row))*row);
        if M == 0 then return if keepSVD then {numcols M, 0} else numcols M;
        (S, U, Vt) = SVD(normalizedM, DivideConquer => true);
    );
    largestGap := (#S, opts.SVDGapThreshold);
    for i from 1 to #S-1 do (
        if S#i == 0 then (
            if first largestGap == #S then largestGap = (i, "infinity");
            break;
        ) else if S#(i-1)/S#i > last largestGap then largestGap = (i, S#(i-1)/S#i);
    );
    if keepSVD then {numcols M - first largestGap, (S, U, Vt)} else numcols M - first largestGap
)


numericalHilbertFunction = method(Options => {Software => M2engine, SVDGapThreshold => 200, verboseOutput => true})
numericalHilbertFunction (List, Ideal, List, ZZ) := numericalInterpolationTable => opts -> (F, I, sampleImagePoints, d) -> ( --outputs the number of L.I. degree d forms vanishing on F(V(I))
    if not all(F | I_*, f -> isHomogeneous f) then (
        F = F | {1_(coefficientRing(ring(I)))};
        sampleImagePoints = apply(sampleImagePoints, p -> point{append(p#Coordinates, 1_(coefficientRing(ring(I))))});
    );
    y := symbol y;
    targetRing := coefficientRing(ring(I))[y_1..y_(#F)];
    allMonomials := basis(d,targetRing);
    if #sampleImagePoints < numcols allMonomials then (
        if opts.verboseOutput then (
            print "Sampling image points ...";
            time sampleImagePoints = join(sampleImagePoints, numericalImageSample(F, I, numcols allMonomials - #sampleImagePoints, Software => opts.Software));
        ) else sampleImagePoints = join(sampleImagePoints, numericalImageSample(F, I, numcols allMonomials - #sampleImagePoints, Software => opts.Software));
    );
    if opts.verboseOutput then (
        print "Creating interpolation matrix ...";
        time interpolationMatrix := matrix(apply(toList(0..<numcols allMonomials), i -> {sub(allMonomials, matrix sampleImagePoints#i)}));
    ) else (
        interpolationMatrix = matrix(apply(toList(0..<numcols allMonomials), i -> {sub(allMonomials, matrix sampleImagePoints#i)}))
    );
    interpolationData := smartNullity(interpolationMatrix, true, verboseOutput => opts.verboseOutput);
    (S, U, Vt) := last interpolationData;
    kernelDim := first interpolationData;
    if opts.verboseOutput then print ("Hilbert function: " | kernelDim);
    new numericalInterpolationTable from {
        symbol hilbertFunctionArgument => d,
        symbol hilbertFunctionValue => kernelDim,
        symbol numericalImageEquations => if kernelDim == 0 then {} else (conjugate Vt^{#S-kernelDim..#S-1})*transpose allMonomials,
        symbol imagePoints => sampleImagePoints,
        symbol interpolationSVD => (S, U, Vt)
    }
)
numericalHilbertFunction (List, Ideal, ZZ) := numericalInterpolationTable => opts -> (F, I, d) -> numericalHilbertFunction(F, I, {}, d, opts)


numericalImageDegree = method(Options => {Software => M2engine, symbol traceTestThreshold => 1e-4, symbol maxMonodromyLoops => 4, symbol maxTraceTests => 3, verboseOutput => true})
numericalImageDegree (List, Ideal, Point) := pseudoWitnessSet => opts -> (F, I, sourcePoint) -> ( --outputs the degree of F(V(I))
    y := symbol y;
    targetRing := (coefficientRing(ring(I)))[y_1..y_(#F)];
    dims := numericalDims(F, I, sourcePoint);
    pullbackSliceData := randomCombinations(F, last dims, true);
    sliceTranslation := transpose sub(matrix{last pullbackSliceData}, matrix sourcePoint);
    pullbackSlice := (last pullbackSliceData) - flatten entries sliceTranslation;
    sliceCoefficients := promote((first pullbackSliceData) | (-1)*sliceTranslation, targetRing);
    fiberSlice := randomCombinations(gens(ring(I)) | {1000_(ring(I))}, (first dims) - (last dims), false);
    fiberSlice = fiberSlice - flatten entries sub(matrix{fiberSlice}, matrix sourcePoint);
    squaredUpSource := (if I == 0 then {} else randomCombinations(I_*, #gens(ring(I)) - first dims, false));
    startSystem := squaredUpSource | fiberSlice | pullbackSlice;
    intersectionPointPairs := smartEval(F, {sourcePoint}, true);
    numFailedTraceTests := 0;
    while numFailedTraceTests < opts.maxTraceTests do (
	numRepetitiveMonodromyLoops := 0;
        if opts.verboseOutput then print "Tracking monodromy loops ...";
	while numRepetitiveMonodromyLoops < opts.maxMonodromyLoops do (
	    isRepetitiveMonodromyLoop := true;
	    possiblyNewIntersectionPointPairs := smartEval(F, monodromyLoop(F, last dims, startSystem, apply(intersectionPointPairs, pair -> first pair), Software => opts.Software), true);
	    for possiblyNewPair in possiblyNewIntersectionPointPairs do (
		if all(intersectionPointPairs, existingPair -> not point last existingPair == point last possiblyNewPair) then (
		    intersectionPointPairs = append(intersectionPointPairs, possiblyNewPair);
		    isRepetitiveMonodromyLoop = false;
                    numFailedTraceTests = 0;
                );
            );
	    if isRepetitiveMonodromyLoop then numRepetitiveMonodromyLoops = numRepetitiveMonodromyLoops + 1
	    else numRepetitiveMonodromyLoops = 0;
            if opts.verboseOutput then print ("Points found: " | #intersectionPointPairs);
        );
        if opts.verboseOutput then print("Running trace test ...");
	if traceTest(F, last dims, startSystem, intersectionPointPairs, Software => opts.Software, traceTestThreshold => opts.traceTestThreshold, verboseOutput => opts.verboseOutput) then (
            if opts.verboseOutput then print("Degree of image: " | #intersectionPointPairs);
            return new pseudoWitnessSet from {
                symbol isCompletePseudoWitnessSet => true,
                symbol imageDegreeLowerBound => #intersectionPointPairs,
                symbol map => F,
                symbol equations => I,
                symbol sourceSlice => transpose matrix{fiberSlice},
                symbol imageSlice => sliceCoefficients*((transpose vars targetRing) || matrix{{1_targetRing}}),
                symbol witnessPointPairs => apply(intersectionPointPairs, pair -> (first pair, point last pair))
            };
        );
        numFailedTraceTests = numFailedTraceTests + 1;
        if opts.verboseOutput then print "Failed trace test!";
        if numFailedTraceTests == opts.maxTraceTests then break;
        newPointPair := first smartEval(F, {smartSample(I, Software => opts.Software)}, true);
        pullbackSliceData = randomCombinations(F, last dims, true);
        sliceTranslation = transpose sub(matrix{last pullbackSliceData}, matrix first newPointPair);
        pullbackSlice = (last pullbackSliceData) - flatten entries sliceTranslation;
        sliceCoefficients = promote((first pullbackSliceData) | (-1)*sliceTranslation, targetRing);
	fiberSlice = randomCombinations(gens(ring(I)) | {1000_(ring(I))}, (first dims) - (last dims), false);
        fiberSlice = fiberSlice - flatten entries sub(matrix{fiberSlice}, matrix sourcePoint);
	squaredUpSource = (if I == 0 then {} else randomCombinations(I_*, #gens(ring(I)) - first dims, false));
	newStartSystem := squaredUpSource | fiberSlice | pullbackSlice;
        intersectionPointPairs = smartTrack(startSystem, newStartSystem, apply(intersectionPointPairs, pair -> first pair), true, Software => opts.Software);
        intersectionPointPairs = smartEval(F, intersectionPointPairs, true);
        if all(intersectionPointPairs, pair -> not point last pair == point last newPointPair) then (
            intersectionPointPairs = append(intersectionPointPairs, newPointPair);
            numFailedTraceTests = 0;
            print "Added new image point";
        );
	startSystem = newStartSystem;
    );
    if opts.verboseOutput then (
        print("Degree of image is strictly greater than " | #intersectionPointPairs);
        print("Consider increasing maxMonodromyLoops and maxTraceTests, or reparametrizing, for a better result.");
    );
    new pseudoWitnessSet from {
        symbol isCompletePseudoWitnessSet => false,
        symbol imageDegreeLowerBound => #intersectionPointPairs,
        symbol map => F,
        symbol equations => I,
        symbol sourceSlice => transpose matrix{fiberSlice},
        symbol imageSlice => sliceCoefficients*((transpose vars targetRing) || matrix{{1_targetRing}}),
        symbol witnessPointPairs => apply(intersectionPointPairs, pair -> (first pair, point last pair))
    }
)
numericalImageDegree (List, Ideal) := pseudoWitnessSet => opts -> (F, I) -> (
    if opts.verboseOutput then (
        print "Sampling point in source ...";
        time sourcePoint := smartSample(I, Software => opts.Software);
    ) else sourcePoint = smartSample(I, Software => opts.Software);
    numericalImageDegree(F, I, sourcePoint, opts)
)


smartTrack = method(Options => {Software => M2engine})
smartTrack (List, List, List, Boolean) := List => opts -> (startSystem, targetSystem, startSolutions, doRefinements) -> (
    C := coefficientRing(ring(first(startSystem)));
    targetSolutions := select(track(startSystem, targetSystem, startSolutions, gamma => random(C), Software => opts.Software), targetSolution -> targetSolution#SolutionStatus == Regular);
    if not doRefinements then return targetSolutions else refine(targetSystem, targetSolutions, Bits => precision(C))
)


smartEval = method()
smartEval (List, List, Boolean) := List => (F, upstairsPoints, includeUpstairs) -> (
    matrixF := matrix{F}; 
    if includeUpstairs then apply(upstairsPoints, p -> (p, sub(matrixF, matrix p)))
    else apply(upstairsPoints, p -> sub(matrixF, matrix p))
)


randomCombinations = method()
randomCombinations (List, ZZ, Boolean) := List => (polys, c, keepCoeffs) -> ( --outputs a list of c random linear combinations of polys
    C := coefficientRing(ring(first polys));
    randomCoefficients := random(C^c, C^#polys);
    if not keepCoeffs then flatten entries(promote(randomCoefficients,ring(first polys))*transpose(matrix{polys}))
    else (randomCoefficients, flatten entries(promote(randomCoefficients,ring(first polys))*transpose(matrix{polys})))
)


monodromyLoop = method(Options => {Software => M2engine})
monodromyLoop (List, ZZ, List, List) := List => opts -> (F, imageDim, startSystem, startSolutions) -> (
    C := coefficientRing(ring(first F));
    intermediateSystem1 := drop(startSystem, -imageDim) | randomCombinations(F | {1000_(ring(first(F)))}, imageDim, false);
    intermediateSystem2 := drop(startSystem, -imageDim) | randomCombinations(F | {1000_(ring(first(F)))}, imageDim, false);
    intermediateSolutions1 := smartTrack(startSystem, intermediateSystem1, startSolutions, false, opts);
    if #intermediateSolutions1 == 0 then return {};
    intermediateSolutions2 := smartTrack(intermediateSystem1, intermediateSystem2, intermediateSolutions1, false, opts);
    if #intermediateSolutions2 == 0 then return {};
    smartTrack(intermediateSystem2, startSystem, intermediateSolutions2, false, opts)
)


traceTest = method(Options => {Software => M2engine, traceTestThreshold => 1e-4, verboseOutput => true})
traceTest (List, ZZ, List, List) := Boolean => opts -> (F, imageDim, startSystem, intersectionPointPairs) -> (
    C := coefficientRing(ring(first F));
    startUpstairsPoints := apply(intersectionPointPairs, pair -> first pair);
    startDownstairsPoints := apply(intersectionPointPairs, pair -> last pair);
    randomTranslation := 10*flatten entries(map(C^1, C^(#startSystem - imageDim), 0) | random(C^1, C^imageDim));
    gammas := {random(C), random(C)};
    firstStepSystem := startSystem + (first gammas)*randomTranslation;
    secondStepSystem := startSystem + (last gammas)*randomTranslation;
    firstStepUpstairsPoints := smartTrack(startSystem, firstStepSystem, startUpstairsPoints, true, Software => opts.Software);
    if not #firstStepUpstairsPoints == #startUpstairsPoints then return false;
    firstStepDownstairsPoints := smartEval(F, firstStepUpstairsPoints, false);
    secondStepUpstairsPoints := smartTrack(startSystem, secondStepSystem, startUpstairsPoints, true, Software => opts.Software);
    if not #secondStepUpstairsPoints == #startUpstairsPoints then return false;
    secondStepDownstairsPoints := smartEval(F, secondStepUpstairsPoints, false);
    traceList := (1/first gammas)*(firstStepDownstairsPoints - startDownstairsPoints) - (1/last gammas)*(secondStepDownstairsPoints - startDownstairsPoints);
    if opts.verboseOutput then print("Trace test: " | toString norm(2,sum(traceList)));
    norm(2,point{sum(traceList)}) < opts.traceTestThreshold
)


isOnImage = method(Options => {Software => M2engine})--add threshold for point equality here and throughout?
isOnImage (pseudoWitnessSet, Point) := Boolean => opts -> (W, p) -> (
    if not W.isCompletePseudoWitnessSet then print "Warning: not a complete pseudo-witness set! May return false negative.";
    F := W.map;
    I := W.equations;
    fiberSlice := flatten entries W.sourceSlice;--deal with F(V(I)) dominates separately
    targetVariables := gens ring((W.imageSlice)_(0,0));
    pullbackSlice := flatten entries sub(W.imageSlice, apply(toList(0..<#targetVariables), i -> targetVariables#i => F#i));
    squaredUpSource := (if I == 0 then {} else randomCombinations(I_*, #gens(ring(I)) - #fiberSlice - #pullbackSlice, false));
    startUpstairsPoints := apply(W.witnessPointPairs, pair -> first pair);
    newPullbackSliceData := randomCombinations(F, #pullbackSlice, true);
    sliceCoefficients := first newPullbackSliceData;
    newPullbackSlice := last newPullbackSliceData;
    newPullbackSlice = newPullbackSlice - flatten entries (sliceCoefficients * promote(transpose(matrix p), coefficientRing(ring(I))));
    targetUpstairsPoints := smartTrack(squaredUpSource | fiberSlice | pullbackSlice, squaredUpSource | fiberSlice | newPullbackSlice, startUpstairsPoints, true, opts);
    any(smartEval(F, targetUpstairsPoints, false), q -> point q == p)
    )
isOnImage (List, Ideal, Point) := Boolean -> (F, I, p) -> isOnImage(numericalImageDegree(F, I), p)


beginDocumentation()

--Documention--
--<<docTemplate
doc ///
    Key
    	NumericalImplicitization
    Headline
    	a Macaulay2 implicitization package
    Description
    	Text
	    Allows for user-friendly computation of the basic invariants of the image of a polynomial map.  Based on numerical algebraic geometry.  The techniques used are interpolation, homotopy continuation and monodromy.  NumericalImplicitization is geared toward large-scale and applied problems, where symbolic methods are too time consuming or fail to terminate.  Current implementation is for irreducible source varieties, affine or projective, and maps that are not necessarily finite-to-one.
///

doc ///
    Key
    	numericalImageSample
	(numericalImageSample, List, Ideal, ZZ)
	(numericalImageSample, List, Ideal)
    Headline
    	samples a general point from the image of a variety
    Usage
    	numericalImageSample(F, I, s)
	numericalImageSample(F, I)
    Inputs
    	F:List
	    of polynomials, specifying a map
	I:Ideal
	    which is prime, specifying a source variety V(I)
	s:ZZ
	    the number of points to sample in F(V(I))
    Outputs
    	:List
	    of sample points on F(V(I)))
    Description
	Text
	    Computes a list of sample points on the image of a variety numerically.	    
        Example
            R = CC[x_(1,1)..x_(3,5)]
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            numericalImageSample(F, ideal 0_R)
///

doc ///
    Key
    	numericalImageDim
	(numericalImageDim, List, Ideal, Point)
	(numericalImageDim, List, Ideal)
    Headline
    	computes the dimension of the image of a variety
    Usage
    	numericalImageDim(F, I, p)
	numericalImageDim(F, I)
    Inputs
    	F:List
	    of polynomials, specifying a map
	I:Ideal
	    which is prime, specifying a source variety V(I)
	p:Point
	    a sample point on V(I)
    Outputs
    	:ZZ
	    the dimension of F(V(I)))
    Description
	Text
	    Computes the dimension of the image of a variety numerically.
        Example
            R = CC[x_(1,1)..x_(3,5)]
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            numericalImageDim(F, ideal 0_R)
        Text
            The following example verifies part of the Alexander-Hirschowitz theorem: the 14th secant variety of the 4th Veronese of P^4 has affine dimension 69, rather than 70.
        Example
            R = CC[a_(1,1)..a_(14,5)]
            F = sum(1..14, i -> flatten entries basis(4, R, Variables=>toList(a_(i,1)..a_(i,5))));
            time numericalImageDim(F, ideal 0_R)
///

doc ///
    Key
    	numericalHilbertFunction
	(numericalHilbertFunction, List, Ideal, List, ZZ)
	(numericalHilbertFunction, List, Ideal, ZZ)
    Headline
    	computes the values of the Hilbert function for the image of a variety
    Usage
    	numericalHilbertFunction(F, I, S, d)
	numericalHilbertFunction(F, I, d)
    Inputs
    	F:List
	    of polynomials, specifying a map
	I:Ideal
	    which is prime, specifying a source variety V(I)
	S:List
	    of general points on F(V(I))
    	d:ZZ
	    the argument of the Hilbert function of F(V(I))
    Outputs
    	:numericalInterpolationTable
	    containing the number of linearly independent degree d forms in the ideal of the projective closure of F(V(I)), along with approximations of those forms
    Description
	Text
	    Computes values of the Hilbert function of the image of a variety, by numerical interpolation.  This technique circumvents the calculation of the kernel of the associated ring map.
        Example
            R = CC[x_(1,1)..x_(3,5)]
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            numericalHilbertFunction(F, ideal 0_R, 2)
    SeeAlso
    	numericalInterpolationTable
///

doc ///
    Key
    	numericalInterpolationTable
        (net, numericalInterpolationTable)
        hilbertFunctionArgument
        hilbertFunctionValue
        numericalImageEquations
        imagePoints
        interpolationSVD
    Headline
    	the class of all numericalInterpolationTables
    Description
	Text
    	    This type is a hashtable storing the output of a polynomial interpolation computation, with the following keys: 
        Code
            UL {
                {TEX "\\bf hilbertFunctionArgument"},
                TEX "\\bf hilbertFunctionValue",
                TEX "\\bf numericalImageEquations",
                TEX "\\bf imagePoints",
                TEX "\\bf interpolationSVD"
                }
        Example
            R = CC[x_(1,1)..x_(3,5)]
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            T = numericalHilbertFunction(F, ideal 0_R, 2)
            (T.hilbertFunctionArgument, T.hilbertFunctionValue)
            numrows T.numericalImageEquations
    SeeAlso
    	numericalHilbertFunction
///

doc ///
    Key
        SVDGapThreshold
        [numericalHilbertFunction, SVDGapThreshold]
    Headline
    	specify minimal threshold for numerical rank
    Usage
        numericalHilbertFunction(..., SVDGapThreshold => 200)
    Description
	Text
    	    Specifies the minimal gap (= ratio of consecutive singular values) for determining the numerical rank of a matrix. If the largest gap is greater than this threshold, then all singular values after the largest gap are considered as numerically zero; if all gaps are less than this threshold, then the matrix is considered numerically full rank.
    SeeAlso
        numericalHilbertFunction
///

doc ///
    Key
        verboseOutput
        [numericalHilbertFunction, verboseOutput]
    	[numericalImageDegree, verboseOutput]
    Headline
    	display detailed output
    Usage
        numericalImageDegree(..., verboseOutput => true)
    Description
	Text
    	    Determines whether or not detailed output is displayed during an interpolation or monodromy computation.
    SeeAlso
        numericalHilbertFunction
    	numericalImageDegree
///

doc ///
    Key
    	numericalImageDegree
	(numericalImageDegree, List, Ideal, Point)
	(numericalImageDegree, List, Ideal)
    Headline
    	computes the degree of and a pseudo-witness set for the image of a variety
    Usage
    	numericalImageDegree(F, I, p)
	numericalImageDegree(F, I)
    Inputs
    	F:List
	    of polynomials, specifying a map
	I:Ideal
	    which is prime, specifying a source variety V(I)
	p:Point
	    a general point on F(V(I))
    Outputs
    	:pseudoWitnessSet
	    containing the degree of the projective closure of F(V(I)), along a pseudo-witness set for F(V(I))
    Description
	Text
	    Computes the degree of the image of a variety, along with a pseudo-witness set for it, by tracking monodromy loops with homotopy continuation and then applying the trace test.  If the trace test fails, only a lower bound for the degree and an incomplete pseudo-witness set is returned. This technique circumvents the calculation of the kernel of the associated ring map.
        Example
            R = CC[x_(1,1)..x_(3,5)]
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            numericalImageDegree(F, ideal 0_R)
    SeeAlso
    	pseudoWitnessSet
///

doc ///
    Key
    	pseudoWitnessSet
        (net, pseudoWitnessSet)
        isCompletePseudoWitnessSet
        imageDegreeLowerBound
        sourceSlice
        imageSlice
        witnessPointPairs
    Headline
    	the class of all pseudoWitnessSets
    Description
	Text
            This type is a hashtable storing the output of a pseudo-witness set computation using monodromy, with the following keys:
        Code
            UL {
                {TEX "\\bf isCompletePseudoWitnessSet: whether or not the witness set has passed the trace test"},
                TEX "\\bf imageDegreeLowerBound: the number of image points found thus far by monodromy",
                TEX "\\bf map: the defining map whose image is under consideration",
                TEX "\\bf equations: the defining ideal of the source variety",
                TEX "\\bf sourceSlice: the pullback of imageSlice under the map",
                TEX "\\bf imageSlice: a general complementary-dimensional linear space to the image",
                TEX "\\bf witnessPointPairs: a list of 2-point sequences where the first point lies on V(I) and the second point is the image of the first under F and also lies on imageSlice"
                }
        Example
            R = CC[x_(1,1)..x_(3,5)]
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            W = numericalImageDegree(F, ideal 0_R, verboseOutput => false)
            W.isCompletePseudoWitnessSet
            #W.witnessPointPairs
    SeeAlso
    	numericalImageDegree
///

doc ///
    Key
        traceTestThreshold
    	[numericalImageDegree, traceTestThreshold]
    Headline
    	specify threshold for trace test
    Usage
        numericalImageDegree(..., traceTestThreshold => 1e-7)
    Description
	Text
    	    Sets the threshold for a pseudo-witness set to pass the trace test. The trace test for a complete pseudo-witness set is 0; large nonzero values indicate failure (the larger the value, the worse the failure).
    Caveat
        Setting the value of this threshold too high may result in the trace test returning false positives.
    SeeAlso
    	numericalImageDegree
        pseudoWitnessSet
///

doc ///
    Key
        maxMonodromyLoops
    	[numericalImageDegree, maxMonodromyLoops]
    Headline
    	specify maximum number of repetitive monodromy loops
    Usage
        numericalImageDegree(..., maxMonodromyLoops => 10)
    Description
	Text
    	    Sets the maximum number of repetitive monodromy loops when computing a pseudo-witness set. A repetitive monodromy loop is one where no new intersection points in the image are discovered.
    SeeAlso
    	numericalImageDegree
        pseudoWitnessSet
///

doc ///
    Key
        maxTraceTests
    	[numericalImageDegree, maxTraceTests]
    Headline
    	specify maximum number of trace tests to run
    Usage
        numericalImageDegree(..., maxTraceTests => 5)
    Description
	Text
    	    Sets the maximum number of times the trace test will run when computing a pseudo-witness set. 
    SeeAlso
    	numericalImageDegree
///

doc ///
    Key
        [numericalImageSample, Software]
        [numericalImageDim, Software]
        [numericalHilbertFunction, Software]
    	[numericalImageDegree, Software]
        [isOnImage, Software]
    Headline
    	specify software for homotopy continuation
    Usage
        numericalImageSample(..., Software => M2engine)
        numericalImageDim(..., Software => M2engine)
        numericalHilbertFunction(..., Software => M2engine)
        numericalImageDegree(..., Software => M2engine)
        isOnImage(..., Software => M2engine)
    Description
	Text
    	    Specifies the software used in polynomial homotopy continuation (used for path tracking) and numerical irreducible decompositions (used for sampling points).
    SeeAlso
        numericalImageSample
        numericalImageDim
        numericalHilbertFunction
    	numericalImageDegree
        isOnImage
///

doc ///
    Key
    	isOnImage
	(isOnImage, pseudoWitnessSet, Point)
	(isOnImage, List, Ideal, Point)
    Headline
    	determines if a point lies on the image of a variety
    Usage
    	isOnImage(W, p)
	isOnImage(F, I, p)
    Inputs
        W:pseudoWitnessSet
            a hash table, containing the degree of the projective closure of F(V(I)), along a pseudo-witness set for F(V(I))
	p:Point
	    a general point on F(V(I))
        F:List
	    of polynomials, specifying a map
	I:Ideal
	    which is prime, specifying a source variety V(I)
    Outputs
    	:Boolean
	    whether or not the point p lies on F(V(I))
    Description
	Text
	    Determines if a point in the ambient target space lies on the image of a variety. 
        Example
            R = CC[x_(1,1)..x_(3,5)]; I = ideal 0_R;
            F = (minors(3, genericMatrix(R, 3, 5)))_*;
            W = numericalImageDegree(F, I, verboseOutput => false)
            p = numericalImageSample(F, I)
            isOnImage(W, p)
    SeeAlso
    	pseudoWitnessSet
        numericalImageDegree
///

TEST /// -- embedding cubic surface (with 3 singular points) in P^3 via 5 sections of O(2)
d = dim ker map(QQ[x,y,z,w]/ideal(x^3 - y*z*w), QQ[a_1..a_5], {x*w + 2*x*y, x*w-3*y^2, z^2, x^2 + y^2 + z^2 - w^2, 3*y*w - 2*x^2})
-- kernel takes ~ 5 seconds
R = CC[x,y,z,w]
I = ideal(x^3 - y*z*w)
F = {x*w + 2*x*y, x*w-3*y^2, z^2, x^2 + y^2 + z^2 - w^2, 3*y*w - 2*x^2}
assert(numericalImageDim(F, I) == d) -- numericalImageDim takes ~1.5 seconds
///

TEST ///
R = CC[s,t]
F = flatten entries basis(4, R) - set{s^2*t^2} -- Rational quartic curve in P^3
h5 = numcols basis(5, ker map(QQ[s,t], QQ[x,y,z,w], {s^4,s^3*t,s*t^3,t^4}))
assert(numericalHilbertFunction(F, ideal(0_R), 5) == h5)
///

end--

installPackage("NumericalImplicitization", RemakeAllDocumentation => true)
viewHelp "NumericalImplicitization"
