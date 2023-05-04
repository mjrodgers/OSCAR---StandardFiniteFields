using Oscar

# NOTE: These give missing features to OSCAR/Nemo that will likely be added in the near future.
function (k::Nemo.FpField)(a::Vector)
  @assert length(a) == 1
  return k(a[1])
end
function (k::FqPolyRepField)(a::Vector)
  return k(polynomial(GF(ZZ(characteristic(k))), a))
end
function coords(x::FinFieldElem)
    return absolute_coordinates(x)
end
function coords(x::T) where T <: Union{fpFieldElem, FpFieldElem}
    return [x]
end


# NOTE: We piggyback on the _attrs (type Dict{Symbol, Any}) property to define:
# is_standardfinitefield (bool)
# is_standardprimefield (bool)
# primitivepowersintowerbasis (matrix)
# towerbasis (also matrix - inverse of primitivepowersintowerbasis)
# steinitzprimedegree (double-indexed dict:
#                    stpd[r][k] will be integer corresponding to Steinitz number for polynomial fr_k)
# standardextensions (Dict{Integer, FField})
# NOTE I think a blanket overwrite of getproperty/setproperty! has potential for conflict with other packages
#       that also want to use custom properties...
# TODO We should give some type checking on these bonus properties
# TODO and also redefine propertynames
_propertysymbols = [:is_standardfinitefield, :is_standardprimefield, :primitivepowersintowerbasis, :towerbasis, :steinitzprimedegree, :standardextensions]
function Base.setproperty!(F::FinField, v::Symbol, c)
    if v == :primitivepowersintowerbasis
        if !isdefined(F, :__attrs)
            setfield!(F, :__attrs, Dict{Symbol, Any}(v => c))
            push!(getfield(F, :__attrs), :towerbasis => inv(c))
        else
            push!(getfield(F, :__attrs), v =>c)
            push!(getfield(F, :__attrs), :towerbasis => inv(c))
        end
    elseif v == :towerbasis
        error()
    elseif v in _propertysymbols
        if !isdefined(F, :__attrs)
            setfield!(F, :__attrs, Dict{Symbol, Any}(v => c))
        else
            push!(getfield(F, :__attrs), v =>c)
        end
    else
        setfield!(F, v, c)
    end
end

function Base.getproperty(F::FinField, v::Symbol)
    if v == :is_standardfinitefield
        if !isdefined(F, :__attrs) || !haskey(getfield(F, :__attrs), :is_standardfinitefield)
            return false
        else
            return get(getfield(F, :__attrs), :is_standardfinitefield, false)
        end
    elseif v == :is_standardprimefield
        if !isdefined(F, :__attrs) || !haskey(getfield(F, :__attrs), :is_standardprimefield)
            return false
        else
            return get(getfield(F, :__attrs), :is_standardprimefield, false)
        end
    elseif v in _propertysymbols
        if !isdefined(F, :__attrs)
            error()
        else
            return get(getfield(F, :__attrs), v, nothing)
        end
    else
        return getfield(F, v)
    end
end


# TODO: Lübeck speeds this up by caching triples [q,m,a] resulting from this
function standardaffineshift(q::ZZRingElem, i)
    m = div(4*q, 5)
    while gcd(m,q) != 1
        m -= 1
    end
    a = div(2*q, 3)
    return mod((m*i + a), q)
end

# Given a field F and Steinitz number n, give the corresponding field element.
# we REQUIRE that F is a standard finite field TODO: using @assert?
function elementfromsteinitznumber(F::FinField, n)
    p = characteristic(F)
    q = order(F)
    if n < 0 || n > q
        error("We need to have 0 <= n <= q")
    end
    if n == 0
        return zero(F)
    elseif q == p
        return F(n)
    else
        vectorrep = GF(p).(digits(n, base = Int(p)))
        # this forms a linear combo of F.towervasis rows using vectorrep as coefficients,
        # and then convert this vector to an element of F.
        return F(vectorrep * @view F.towerbasis[1:length(vectorrep), :])
    end
end

# Returns an element a in F that is NOT an rth root of unity
# we REQUIRE that F is a standard finite field TODO: using @assert?
function non_rth_root(F::FinField, r)
    q = order(F)
    if mod(q-1, r) == 0
        i = 0
        a = zero(F)
        while a == 0 || a^(div(q-1,r)) == one(F)
            i += 1
            a = elementfromsteinitznumber(F, standardaffineshift(q, i))
        end
        return a
    else
        return nothing
    end
end


function standardirreduciblecoefflist(F::FinField, r, a)
    q = order(F)
    l = zeros(F, Int(r)+1) # NOTE - AbstractAlgebra does not allow this be ZZRingElem
    l[Int(r)+1] = one(F)
    l[1] = a
    l[2] = one(F)
    # inc is the expected number of nonzero coefficients
    inc = 1
    while q^inc < 2*r
        inc += 1
    end
    # allowing non-zero coeffs up to position d
    # after every r attempts allow inc more non-zero coeffs
    d = 0
    count = 0
    qq = 0
    while !is_irreducible(polynomial(F, l))
        if mod(count, r) == 0 && d < r-1
            d += inc
            if d >= r
                d = r-1
            end
            qq = q^(d-1)
        end
        # q can be very very large so Int is not big enough...
        st = digits(standardaffineshift(qq,count), base = BigInt(q), pad = d-1)
        # TODO: we can remove this while loop when digits bug for n = 0 is fixed
        while length(st) < d-1
            push!(st, 0)
        end
        for k in 2:d
            l[k] = elementfromsteinitznumber(F, st[k-1])
        end
        count += 1
    end
    return l
end

# returns the Steinitz number corresponding to the polynomial g(X),
# where f = X^r + g(X) is the standard irreducible polynomial over FF(p, r^(k-1))
function steinitznumberforprimedegree(p,r,k)
    Fp = standardfinitefield(p,1)
    if !haskey(Fp.__attrs, :steinitzprimedegree)
        Fp.steinitzprimedegree = Dict{ZZRingElem, Dict{ZZRingElem, ZZRingElem}}()
    end
    stpd = Fp.steinitzprimedegree
    if !haskey(stpd, r)
        stpd[r] = Dict{ZZRingElem, ZZRingElem}()
    end
    stpdr = stpd[r]
    if !haskey(stpdr,k)
        # now we need to create the polynomial depending on the prime r
        if r == p
            # Artin-Schreier case
            # k = 1 we get [(Xr[1])^p - (Xr[1]) -1]
            # k > 1 we get (Xr[k])^p - (Xr[k]) - (prod(Xr[j] : j in [1..k-1]))^(p-1))
            q = p^(p^(k-1))
            stpdr[k] = (p-1)*(q + div(q,p))
        elseif r == 2 && mod(p,4) == 3
            if k == 1
                # (Xr[1])^2 +1
                stpdr[k] = 1
            elseif k == 2
                a = non_rth_root(standardfinitefield(p,2), r)
                # Xr[2]^2 -a
                stpdr[k] = steinitznumber(-a)
            else
                # Xr[i]^2 - Xr[i-1]
                stpdr[k] = (p-1)*p^(r^(k-2))
            end
        elseif r == 2
            if k == 1
                # Xr[1]^2 -a
                a = non_rth_root(standardfinitefield(p, 1), r)
                stpdr[k] = steinitznumber(-a)
            else
                # Xr[j]^r - Xr[j-1]
                stpdr[k] = (p-1)*p^(r^(k-2))
            end
        else
            # Here we use pseudo-random polynomials...
            F = standardfinitefield(p, r^(k-1))
            if k == 1
                a = -one(F)
            else
                a = -gen(F)
            end
            l = standardirreduciblecoefflist(F,r,a)
            pop!(l)
            while is_zero(l[end])
                pop!(l)
            end
            stpdr[k] = evaluate(polynomial(ZZ, steinitznumber.(l)), order(F))
        end
    end
    return stpdr[k]
end

# x will be represented internally as a polynomial over Fp in the generator of F.
# We need to first convert this to an Fp-vector, then to the corresponding vector
# with respect to the Tower Basis.
# Then we think of this vector as a polynomial (over ZZ) in a temporary indeterminate z,
# and evaluate at z = char(F) to get the Steinitz number.
# NOTE for whatever reason, evaluate(polynomial(), ) is faster than evalpoly()
function steinitznumber(F::FinField, x::FinFieldElem)
    if order(F) == characteristic(F)
        return lift(x)
    end
    v = lift.(absolute_coordinates(x) * F.primitivepowersintowerbasis)
    return evaluate(polynomial(ZZ, v), characteristic(F))
end
function steinitznumber(x::FinFieldElem)
    return steinitznumber(parent(x), x)
end


# describes monomials in tower basis plus their degrees
function std_mon(n)
    error("not implemented")
end
# just return degrees
function std_mon_degs(n)
    if n == 1
        return [ZZ(1)]
    end
    # need the largest prime factor a of n
    nfactorization = factor(ZZ(n))
    nfactors = sort([r for (r,e) in nfactorization])
    a = nfactors[end]
    res = std_mon_degs(div(n,a))
    new = map( x -> lcm( x, a^nfactorization[a] ),res)
    for i = 1:a-1
        append!(res, new)
    end
    return res
end


# map of monomials for degree n -> monomials of degree m by positions
function std_mon_map(n,m)
    d = std_mon_degs(m)
    return [i for i = 1:length(d) if mod(n, d[i]) == 0]
end


# Embed an element x of Fp^n into Fp^m by Steinitz numbers
# where nr = steinitznumber(Fp^n, x)
# I hate hate hate these variable names copied (mostly) from Lübeck
function embedsteinitz(p,n,m,nr)
    if n == m || iszero(nr)
        return nr
    end
    l = digits(nr, base = Int(p))
    m = @view std_mon_map(n,m)[1:length(l)]
    c = zeros(ZZRingElem, m[end])
    c[m] = l
    return evaluate(polynomial(ZZ, c), p)
end



# Given a field K, we construct an extension L with [L:K] = deg
# We use the irreducible polynomial f = X^deg  + g(X)
#    where lcoeffs are the coefficients of g(X).
# We assume b is a generator for K, and so bX will be a generator for L
function _extensionwithtowerbasis(K::FinField, deg, lcoeffs, b::FinFieldElem)
    dK = absolute_degree(K)
    d = Int(dK * deg)
    F = prime_field(K)
    if dK == 1
        p = zeros(K, Int(deg)+1)
        p[1:length(lcoeffs)] = lcoeffs
        p[end] = one(K)
        pmat = identity_matrix(F, Int(deg))
    else
        while length(lcoeffs) < deg
            push!(lcoeffs, zero(K))
        end
        push!(lcoeffs, one(K))
        pK = K.primitivepowersintowerbasis

        # The idea is to collect (bX)^i mod f for 1 in 0..d*dK-1
        # and use this to compute the minimal polynomial of bX over F.
        # Should we just form the polynomial and compute "mod"???
        vec = zeros(F, d)
        vec[1] = one(F)
        v = zeros(K, Int(deg))
        v[1] = one(K)

        vecs = Vector{Vector{FinFieldElem}}(undef, d)
        pols = Vector{Vector{FinFieldElem}}(undef, d)
        pmat = zero_matrix(F, d, d)

        for i in 1:d+1
            # println("i: ", i, " vec: ", vec, " v: ", v)
            if i <= d
                pmat[i, : ] = vec
            end

            p = zeros(F, i)
            p[end] = one(F)

            w = copy(vec)
            piv = findfirst(!iszero, w)
            # TODO : figure out the purpose of this loop and FIX it
            while piv != nothing && isassigned(vecs, piv)
                x = -w[piv]
                if isassigned(pols, piv)
                    # println("p: ", p, " piv ", piv, " pols[piv]: ", pols[piv])
                    p[1:length(pols[piv])] += x .* pols[piv]
                end
                w[piv:d] += x .* @view vecs[piv][piv:d]
                piv = findnext(!iszero, w, piv+1)
            end
            # NOTE : exits the while loop when either piv == nothing, or vecs[piv] is undefined.
            #        what happens if piv == nothing???
            # println("Exiting loop with piv = ", piv)
            if i <= d
                # println(order(K), " ", piv, " ", v, " ", w)
                x = inv(w[piv])
                p .= x .* p
                w .= x .* w
                pols[piv] = copy(p)
                vecs[piv] = copy(w)


                # Multiply by vX and find the next vec in the Tower Basis
                v = collect(coefficients(mod(polynomial(K, pushfirst!(b .* v, zero(K))),
                                             polynomial(K, lcoeffs))))

                while length(v) < deg
                    push!(v, zero(K))
                end
                # println("new v:", v)
                vec = vcat(map( a -> coords(a) * pK, v)...)

            end
        end
        # Now p is the minimal polynomial over F
        # pmat gives the primitive powers in the tower basis for the new extension
    end

    vname = "x" * string(d)
    L, X = FiniteField(polynomial(F, p), vname)
    L.is_standardfinitefield = true
    L.primitivepowersintowerbasis = pmat

    return L

end


function standardfinitefield(p::ZZRingElem,n)
    if !isprime(p)
        error()
    end
    F = GF(p)
    if !F.is_standardprimefield
        F.is_standardprimefield = true
        F.standardextensions = Dict{ZZRingElem, FinField}(1 => F)
        F.primitivepowersintowerbasis = identity_matrix(F, 1)
    end
    ext = F.standardextensions
    if haskey(ext, n)
        return ext[n]
    end

    nfactorization = factor(ZZ(n));
    nfactors = sort([r for (r,e) in nfactorization]);
    lastfactor = nfactors[end]
    nK = div(n,lastfactor)
    K = standardfinitefield(p, nK)

    stn = steinitznumberforprimedegree(p, lastfactor, nfactorization[lastfactor])
    n1 = lastfactor^(nfactorization[lastfactor]-1)
    q1 = p^n1

    # for each element y in this list, we want to
    # 1. call EmbedSteinitz(p, n1, nK, y)
    # 2. this should give a number, we want to use ElementSteinitzNumber to get an element of K.
    l = digits(stn, base = BigInt(q1))
    c = map(y -> elementfromsteinitznumber(K, embedsteinitz(p, n1, nK, y)), l)
    b = elementfromsteinitznumber(K, p^( findfirst(x -> x == div(nK, n1), std_mon_degs(nK))-1))

    L = _extensionwithtowerbasis(K, lastfactor, c, b)
    ext[n] = L
    return L
end




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
