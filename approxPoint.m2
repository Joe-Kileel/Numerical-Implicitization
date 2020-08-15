
-- Find approximate point on variety

realPoint = method(Options => {Tolerance => 1e-10, Iterations => 1000})
realPoint Ideal := Matrix => opts -> I -> (
	p := nelderMead(I, opts, Initial => "random");
	if norm sub(gens I, p) > opts.Tolerance then (
		print "Starting gradient descent";
		p = lineSearch(I, p, opts);
	);
	p
)

-- Nelder–Mead(/downhill simplex/amoeba) method

nelderMead = method(Options => {Tolerance => 1e-6, Iterations => 200, Initial => "standard"})
nelderMead (FunctionClosure, List) := List => opts -> (F, V) -> (
	-- Inputs: F = nonnegative real-valued function, V = full-dim simplex given as (vertices, values)
	-- Output: (real) zero of F (approximate up to opts.Tolerance)
	n := #V - 1;
	counter := 0;
	V = sort(V, last);
	while counter < opts.Iterations do (
		if debugLevel > 1 then print("Using points: " | toString(V/first/entries/first));
		if V#0#1 < opts.Tolerance then (
			print "Found solution to within tolerance";
			break;
		);
		centroid := (1/n)*sum drop(V/first, -1);
		reflected := 2*centroid - V#-1#0; -- alpha = 1
		fR := F(reflected);
		if V#0#1 <= fR and fR < V#-2#1 then (
			if debugLevel > 0 then print("Reflection: " | toString first entries reflected);
			V = append(drop(V, -1), {reflected, fR});
		) else if fR < V#0#1 then (
			expanded := 2*reflected - centroid; -- gamma = 2
			if debugLevel > 0 then print("Expansion: " | toString first entries expanded);
			fE := F(expanded);
			V = prepend(if fE < fR then {expanded, fE} else {reflected, fR}, drop(V, -1));
		) else (
			contracted := (1/2)*(V#-1#0 + centroid); -- rho = 1/2
			fC := F(contracted);
			if fC < V#-1#1 then (
				if debugLevel > 0 then print("Contraction: " | toString first entries contracted);
				V = append(drop(V, -1), {contracted, fC});
			) else (
				if debugLevel > 0 then print "Shrink";
				V = {V#0#0} | apply(#V-1, i -> (1/2)*(V#(i+1)#0 + V#0#0)); -- sigma = 1/2
				V = apply(V, v -> {v, F(v)});
			);
		);
		V = sort(V, last);
		counter = counter+1;
		if counter % 100 == 0 then print("Completed " | toString counter | " iterations");
		if V#-1#1 - V#0#1 < (opts.Tolerance)^(1.5) and V#0#1 > opts.Tolerance then (
			if debugLevel > 0 then print "Stuck in local minimum";
			break;
		);
	);
	V
)
nelderMead Ideal := Matrix => opts -> I -> (
	n := dim ring I;
	k := if instance(coefficientRing ring I, ComplexField) then CC else RR;
	V := if instance(opts.Initial, List) then opts.Initial
		else if opts.Initial === "standard" then simplex n
		else if opts.Initial === "continue" then I.cache#"nelderMeadSimplex"
		else entries(random(k^(n+1), k^n));
	F := x -> norm sub(gens I, x); -- x -> sub(sos, x);
	if not opts.Initial === "continue" then V = apply(V, v -> {matrix{v}, F(matrix{v})});
	V = nelderMead(F, V, opts);
	if V#0#1 > opts.Tolerance then print "Solution not found within tolerance. Try running this function again with Initial => \"continue\", or alternatively use lineSearch";
	I.cache#"nelderMeadSimplex" = V;
	V#0#0
)

simplex = method(Options => { CoefficientRing => RR, Shift => 0, Scale => 1 })
simplex ZZ := List => opts -> n -> (
	(k, a, s) := (opts.CoefficientRing, opts.Shift, opts.Scale);
	v0 := if instance(a, List) then a else a*toList(n:1_k);
	A := entries (matrix{{n:0_k}} || s*id_(k^n));
	A/(v -> v + v0)
)

sort (List, Function) := opts -> (L, f) -> (
	H := hashTable(identity, apply(L, l -> f(l) => l));
	deepSplice join apply(sort keys H, k -> H#k)
)

lineSearch = method(Options => options realPoint)
lineSearch (Ideal, Matrix) := Matrix => opts -> (I, s) -> (
	sos := sum(I_*, g -> g^2);
	grad := diff(vars ring I, sos);
	F := x -> sub(sos, x);
	y := s;
	for i from 1 to opts.Iterations do (
		v := sub(grad, y);
		m := norm v;
		p := -(1/m)*v; -- descent direction
		t := (1/2)*m;
		alpha := 2; -- initial (max) step size
		(F0, F1) := (F(y), F(y + alpha*p));
		while F1 > F0 - alpha*t and alpha > opts.Tolerance do ( -- Armijo-Goldstein condition
			alpha = (1/2)*alpha; -- backtracking
			F1 = F(y + alpha*p);
		);
		if debugLevel > 0 then print("Old: " | toString(F0) | ", new: " | toString(F1));
		y = y + alpha*p;
		if F1 < opts.Tolerance then (
			print "Found solution to within tolerance";
			break;
		);
		if i % 25 == 0 then print("Completed " | toString i | " iterations");
	);
	y
)

end--

restart
load "approxPoint.m2"
debugLevel = 1
printingPrecision = 6

elapsedTime realPoint I
elapsedTime realPoint(I. Iterations => 300)
elapsedTime realPoint(I. Iterations => 1000)
sub(gens I, oo)

elapsedTime p = nelderMead(I, Iterations => 500)
elapsedTime p = nelderMead(I, Initial => "random", Iterations => 500)
elapsedTime p = nelderMead(I, Initial => "random")
elapsedTime p = nelderMead(I, Initial => "continue", Iterations => 1000)

J = sub(I, RR[gens ring I]);
sub(gens I, p)

needsPackage "NumericalImplicitization"
numericalSourceSample(J, point p, 40)

s = sub(random(R^1,R^(#gens R)), RR)
elapsedTime s = lineSearch(I,s,Iterations=>500)
elapsedTime lineSearch(I,p,Tolerance => 1e-16, Iterations => 500)

---------------------------------------

-- Two points in A^3

R = QQ[x,y,z]
I = intersect(ideal(x - 1/4, y - 1/5, z - 1/6), ideal(x - 1/2, y - 2/3, z - 4/5))
I = intersect(ideal(x - (1000 + 1/4), y - (2000 + 1/5), z - (3000 + 1/6)), ideal(x - (1/2 - 2000), y - (2/3 - 1000), z - (4/5 - 3000))) -- nelderMead gives bad output on Initial => "standard" or "random"
guess = simplex(3, Shift => {1e3,2e3,3e3})
guess = simplex(3, Shift => {-2e3,-1e3,-3e3})
nelderMead(I, Initial => guess)

---------------------------------------

-- Rosenbrock function
R = QQ[x,y]
(a,b) = (1,10)
I = ideal(a - x, b*(y - x^2))

V = simplex(2, Shift => {-1,1})
V = apply(V, v -> {matrix{v}, F(matrix{v})})
nelderMead(F, V)

---------------------------------------

-- SO(n)

n = 5
R = RR[a_(1,1)..a_(n,n)]
A = genericMatrix(R,n,n);
I = ideal(A*transpose A - id_(R^n)); -- Can be trapped in local minimum

---------------------------------------

-- Funtf variety

(n,r) = (4,5)
R = QQ[x_(1,1)..x_(n,r)]
A = transpose genericMatrix(R,r,n)
I1 = ideal(A*transpose A - (r/n)*id_(R^n))
I2 = ideal apply(entries transpose A, row -> sum(row, v -> v^2) - 1)
I = I1 + I2

---------------------------------------

R=QQ[x_111,x_121,x_131,x_211,x_221,x_231,x_311,x_321,x_331,x_113,x_123,x_133,x_213,x_223,x_233,x_313,x_323,x_333,x_112,x_122,x_132,x_212,x_222,x_232,x_312,x_322,x_332,x_114,x_124,x_134,x_214,x_224,x_234,x_314,x_324,x_334]
B1=matrix{{x_111,x_112,x_113,x_114},{x_211,x_212,x_213,x_214},{x_311,x_312,x_313,x_314}}
B2=matrix{{x_121,x_122,x_123,x_124},{x_221,x_222,x_223,x_224},{x_321,x_322,x_323,x_324}}
B3=matrix{{x_131,x_132,x_133,x_134},{x_231,x_232,x_233,x_234},{x_331,x_332,x_333,x_334}}
B4=matrix{{x_111-x_121,x_112-x_122,x_113-x_123,x_114-x_124},{x_211-x_221,x_212-x_222,x_213-x_223,x_214-x_224},{x_311-x_321,x_312-x_322,x_313-x_323,x_314-x_324}}
B5=matrix{{x_111-x_131,x_112-x_132,x_113-x_133,x_114-x_134},{x_211-x_231,x_212-x_232,x_213-x_233,x_214-x_224},{x_311-x_321,x_312-x_322,x_313-x_323,x_314-x_324}}
B6=matrix{{x_121-x_131,x_122-x_132,x_123-x_133,x_124-x_134},{x_221-x_231,x_222-x_232,x_223-x_233,x_224-x_234},{x_321-x_331,x_322-x_332,x_323-x_333,x_324-x_334}}
I=ideal(minors(3,B1),minors(3,B2),minors(3,B3),minors(3,B4),minors(3,B5),minors(3,B6));

---------------------------------------

R = QQ[x_1..x_12, y_1..y_12, z_1..z_12]
A = transpose genericMatrix(R,12,3)
cols = pack(toList(0..11),3) | flatten apply(pack(mingle pack(toList(0..11),3), 4), s -> subsets(s,3))
I = ideal apply(cols, c -> det A_c);

---------------------------------------
