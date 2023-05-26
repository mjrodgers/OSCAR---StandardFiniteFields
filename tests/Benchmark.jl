include("StandardFiniteFields.jl")
import .StandardFiniteFields

# The code below is for testing/benchmarking
GAP.Packages.load("StandardFF")

function MyPoly(p,n)
    return defining_polynomial(standard_finite_field(p,n))
end

function GAPPoly(p,n)
    poly = GAP.evalstr( "StandardFiniteField(" * string(p) * ", " * string(n) * ")!.DefiningPolynomial!.CoefficientsOfUnivariatePolynomial")
    poly = polynomial(GF(p), map(x -> GF(p)(x), GAP.gap_to_julia(Vector{GAP.FFE}, poly)))
end

function compare_poly(p,n)
  F = GF(p)
  F.(collect(coefficients(MyPoly(p, n)))) == F.(collect(coefficients(GAPPoly(p, n))))
end
function compare_poly2(p,n)
  F = GF(ZZ(p))
  F.(collect(coefficients(MyPoly(ZZ(p), n)))) == F.(collect(coefficients(MyPoly(Int(p), n))))
end

function test(p::IntegerUnion, r::UnitRange)
    for n in r
        println(n)
        @time standard_finite_field(ZZ(p),n)
        @time standard_finite_field(Int(p),n)
        @time FG = GAP.Globals.StandardFiniteField(Int(p),n)
    end
end

p = ZZ(3)
S = Set([ n for n in 6:64 if !compare_poly(p,n) ])
S2 = Set([ n for n in 6:64 if !compare_poly2(p,n) ])

test(2, 120:140)
test(5, 90:120)
