# The code below is for testing/benchmarking
GAP.Packages.load("StandardFF")

function MyPoly(p,n)
    return defining_polynomial(standardfinitefield(p,n))
end

function GAPPoly(p,n)
    poly = GAP.evalstr( "StandardFiniteField(" * string(p) * ", " * string(n) * ")!.DefiningPolynomial!.CoefficientsOfUnivariatePolynomial")
    poly = polynomial(GF(p), map(x -> GF(p)(x), GAP.gap_to_julia(Vector{GAP.FFE}, poly)))
end

function compare_poly(p,n)
  F = GF(p)
  F.(collect(coefficients(MyPoly(p, n)))) == F.(collect(coefficients(GAPPoly(p, n))))
end

p = ZZ(3)
S = Set([ n for n in 6:64 if !compare_poly(p,n) ])

p = ZZ(5)
for n in 100:150
    println(n)
    @time F = standardfinitefield(p,n)
    @time FG = GAP.Globals.StandardFiniteField(5,n)
end
