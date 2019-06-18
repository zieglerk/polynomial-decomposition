# TODO doctests time out KZ2015/07/19

# related packages:
# - Maple's with(oretools) :: TODO
# - RISC's ore_algebra :: use delta = 0 and sigma = r-th power; fails since only prime fields allowed

'''
For a *single* additive polynomial, we answer the following questions.
- RJF :: What is a rational Jordan Form for the Frobenius operator on the root space? And its species?
- numL :: How many right components of a given exponent exist?
- chains :: How many complete decompositions exist?

Approach
0. assume monic squarefree
1. compute RationalJordanForm (and its species) a la GathenGiesbrechtZiegler
2. use Fripertinger on species to return
   a) generating function for subspace numbers answering (Q1)
   b) number of chains in subspace lattice answering (Q2)
3. reduce general case to assumptions in 0.

Language/design options:
- use "skew multiplication language"
- use "additive composition language"
We opt for the latter in the interest of compatibility with the other packages in the module.

Classes/Objects:
- single eigenvalue's species lam = [m, lamj's]
- whole operator's species LAM = [lam, mu, ...], where lam, mu, ... are as above



'''

from itertools import product
from collections import Counter

# SECTION setup
# =============

p = 2

e = 2
r = p^e

d = 2
q = r^d    # @future: p^d

assert p.is_prime()
assert r.is_power_of(p)
assert q.is_power_of(r)

var('eta', 'theta')
Fr = GF(r, conway=True, prefix='z')    # ground field ...
eta = Fr.gen()                         # ... and its generator
Fq = GF(q, conway=True, prefix='z')    # field extension ...
theta = Fq.gen()                       # ... and its generator

var('x, y')
# no way to restrict to the additives Fq[x; r], so we consider the whole ring R = Fq[x]
R.<x> = PolynomialRing(Fq, x)
# the centre of Fq[x; r] is Fr[x; q] with commutative image S = Fr[y]
S.<y> = PolynomialRing(Fr, y)

def is_additive(f):
    '''
sage: is_additive(0)
True
sage: is_additive(1)
False
sage: is_additive(x)
True
'''
    assert f in R
    f = R(f)
    if f == 0:
        return True
    if f.degree() == 0:
        return False
    for m in f.exponents():
        if not ZZ(m).is_power_of(r):
            return False
    return True

def is_central(f):
    '''TODO maybe faster check over all monomials via dictionary
sage: q, r
(16, 4)
sage: is_additive(x^4)
True
sage: is_central(x^4)
False
sage: is_central(x^16)
True
'''
    assert is_additive(f)
    for m in f.exponents():
        if not ZZ(m).is_power_of(q):
            return False
    for a in f.coefficients():
        if not a in Fr:
            return False
        return True


def is_squarefree(f):
    '''sage: is_squarefree(x^4)
False
sage: is_squarefree(x)
True
sage: is_squarefree(x^4 + x)
True
'''
    assert is_additive(f)
    return (f.derivative().substitute(x=0) != 0)

def centralize(f):
    '''the coefficients of a central polynomial may be written with the generator of the larger field. We don't want that.'''
    assert is_central(f)
    F = PolynomialRing(Fr, x)(f)
    assert f == F
    return F

def tau(f):
    '''maps additive polynomials in the centre Fr[x; q] of R = Fq[x; r] to their commutative image S = Fr[y]
r = 2^2
q = 2^4
f = x^16 + x
sage: tau(f)
y + y
'''
    assert f in R
    f = R(f)
    assert is_central(f)
    n = f.degree().log(q)
    F = S(0)
    coefficients = f.coefficients(sparse=False)
    for i in srange(n+1):
        F += coefficients[q^i]*y^i
    return S(F)

def invtau(F):
    '''inverse map of tau, taking a polynomial from S = Fr[y] and mapping it to (the centre of) R = Fq[x; r]

r = 2^2
q = 2^4
F = y+1
sage: invtau(F)
x^16 + x

'''
    assert F in S
    F = S(F)
    n = F.degree()
    f = R(0)
    coefficients = F.coefficients(sparse=False)
    for i in srange(n+1):
        f += coefficients[i]*x^(q^i)
    assert is_central(f)
    return PolynomialRing(Fr, x)(f)

def gcrc(f,g):
    assert is_additive(f)
    assert is_additive(g)
    if f == R(x):
        return R(x)
    if g == R(x):
        return R(x)
    return gcd(f,g)

def rdiv_with_rem(f, g):
    '''return (q, r) such that f = q o g + r and r minimal.'''
    if f == R(0):
        return (0, 0)
    m = f.degree().log(r)
    n = g.degree().log(r)
    if m < n:
        return (0, f)
    if m == n:
        a = f.leading_coefficient()
        b = g.leading_coefficient()
        c = a/b
        quo = c*x
        rem = f - c*g
        assert is_additive(quo)
        assert is_additive(rem)
        assert rem.degree() < g.degree()
        assert f == quo.subs(g) + rem
        return (quo, rem)
    a = f.leading_coefficient()
    b = g.leading_coefficient()
    c = a/b^(r^(m - n))
    quo1 = c*x^(r^(m - n))
    rem1 = f - quo1.subs(g)
    assert rem1.degree() < f.degree()
    quo2, rem2 = rdiv_with_rem(rem1, g)
    quo = quo1 + quo2
    rem = rem2
    assert f == quo.subs(g) + rem
    return (quo, rem)

def dot_product(polys, scalars):
    return sum(p*a for p, a in zip(polys, scalars))

def linear_relation(polys):
    '''for a list of additive polynomials from Fq[x; r] return a list of elements of coeffients from Fr (!) such that their scalar product is zero; return None if none exists.

Since this list is built up incrementally, we assume that there is no linear relation amoung the first m-1 polynomials and we can set the last scalar to 1.

sage: linear_relation([0])
[1]
sage: linear_relation([x, x^2])
sage: linear_relation([x, x^2, x^2+x])
(1, 1, 1)

'''
    if R(0) in polys:
        i = polys.index(R(0))
        coeffs = [0] * len(polys)
        coeffs[i] = R(1)
        return coeffs
    m = len(polys)
    if m == 1:
        '''single entry is nonzero due to previous if-clause.'''
        return None
    for head in product(Fr, repeat=m - 1):
        scalars = head + (R(1),)
        if dot_product(polys, scalars) == R(0):
            return scalars
    return None

def mclc(h):
    '''return minimal monic central f, such that f = g o h for some g.

You can then always the cofactor ''g'' via rdiv_with_rem(f,h)[0].

remainders have at most n coefficients from Fq, thus dimension n*d over Fr.

d*n+1 remainders suffice for a non-trivial relations and we take x^(q^j) for j = 0, ..., n*d

'''
    a = h.leading_coefficient()
    n = h.degree().log(r)
    if is_central(h/a):
        return h/a
    centrals = [x]
    remainders = [x]
    for j in srange(1, d*n+1):
        cent = x^(q^j)
        rem = rdiv_with_rem(cent, h)[1]
        centrals += [cent]
        remainders += [rem]
        if linear_relation(remainders):
            coeffs = linear_relation(remainders)
            central = dot_product(coeffs, centrals)
            central = centralize(central)
            return central
    print 'Warning! No bound found in due time.'

def random_additive(n, squarefree=False, central=False):
    '''return random monic r-additive polynomial of exponent n.

    options:
    - squarefree (default: False)
    - central (default: False)

    target degree r^n = q^(n * log_q r) = q^(n/d)
    '''
    if central:
        d = q.log(r)
        if d == 1:
            return random_additive(n, squarefree=squarefree)
        assert not squarefree, "the target degree r^n is not a power of q"
        m = n.divide_knowing_divisible_by(d)
        F = y^m + S.random_element(degree=m-1)
        return invtau(F)
    f = x^(r^n)
    for i in srange(n):
        coeff = Fq.random_element()
        if squarefree and i == 0:
            while coeff == 0:
                coeff = Fq.random_element()
        f += coeff*x^(r^i)
    assert is_additive(f)
    return f

def test_setup():
    F = y+3*eta
    G = y+eta^2+2*eta
    f = invtau(F)
    g = invtau(G)
    print "Two central polynomials", f, g
    print "and their gcrc", gcrc(f, g)
    n = 4
    f = random_additive(n)
    g = random_additive(n-2)
    print "Two random additive polynomials", f, g
    quo, rem = rdiv_with_rem(f,g)
    print "and their quotient and remainder (checked)", quo, rem, f == quo.subs(g) + rem
    n = 2
    f = random_additive(n, squarefree=True)
    print "A random squarefree additive", f
    F = mclc(f)
    print "and its mclc", F




























# SECTION RJF
# ===========

def rat_jordan_block(u, e):
    '''produce a rational Jordan block for u with multiplicity e.

sage: r = 3^2
sage: q = 3^4
sage: rat_jordan_block(y + 1, 2)
/home/zieglerk/local/share/sage/src/bin/sage-ipython:287: DeprecationWarning: invocation of block_matrix with just a list whose length is a perfect square is deprecated. See the documentation for details.
[2 1]
[0 2]
sage: M = rat_jordan_block(y^2 + 1, 2)
[0 2 1 0]
[1 0 0 1]
[0 0 0 2]
[0 0 1 0]

'''
    assert u.is_monic()
    # assert u.is_irreducible()
    C = companion_matrix(u)
    diag = block_diagonal_matrix([C]*e, subdivide=False)
    if e == 1:
        return diag
    m = u.degree()
    I = identity_matrix(m)
    O = zero_matrix(m, m)
    offlist = [O]
    for i in range(e-1):
        offlist += [I] + [O]*e
    offdiag = block_matrix(offlist, subdivide=False)
    return diag + offdiag


def RJF(f, species_only=False):
    '''following Algorithm 4.10 (algo:ratJNF) of GathenGiesbrechtZiegler2015, we compute the rational RJF of the Frobenius automorphism on the root space of f. Return type: matrix

Optionally, we return only the species of the rational Jordan form. Return type: list of lists [[deg u_1, lambda_11, lambda_12, ..., lambda_1k_1], [deg u_2, lambda_21, lambda_22, ..., lambda_2k_2], ...]

# one rational Jordan block of size 2
sage: f = x^16 + (theta^2 + 1)*x
sage: RJF(f)
[     0 z2 + 1]
[     1      1]
sage: RJF(f, species_only=True)
[[2, 1]]

sage: f = x^16 + (z4^3 + z4^2 + 1)*x
sage: RJF(f)
[ 0 z2]
[ 1 z2]


# two distinct rational Jordan blocks of size 1 each
sage: f = x^16 + (theta^3 + 1)*x^4 + (theta^2 + theta + 1)*x
sage: RJF(f)
[ 1| 0]
[--+--]
[ 0|z2]
sage: RJF(f, species_only=True)
[[1, 1], [1, 1]]


sage: f = x^16 + z4^2*x^4 + (z4^3 + z4)*x
sage: RJF(F)
[    z2|     0]
[------+------]
[     0|z2 + 1]

# twice the same rational Jordan block of size 1

sage: f = x^16 + x
sage: RJF(f)
[1|0]
[-+-]
[0|1]
sage: RJF(f, species_only=True)
[[1, 1], [1, 1]]


Uk is (y + z2 + 1) * (y^2 + y + z2 + 1)
[z2 + 1|     0      0]
[------+-------------]
[     0|     0 z2 + 1]
[     0|     1      1]
sage: f
x^64 + (z4^2 + 1)*x^16 + (z4 + 1)*x^4 + (z4^3 + z4 + 1)*x

f = random_additive(3); RJF(f)
Uk is (y + z2) * (y + z2 + 1)^2
[    z2|     0      0]
[------+-------------]
[     0|z2 + 1      1]
[     0|     0 z2 + 1]
sage: f
x^64 + (z4^3 + z4^2 + z4 + 1)*x^16 + (z4^3 + z4^2 + z4)*x^4 + (z4^2 + z4)*x

    '''
    assert is_additive(f), "f is not additive"
    assert is_squarefree(f), "f is additive, but not squarefree"
    fstar = mclc(f)
    minpoly = tau(fstar).factor()
    t = len(minpoly)
    D = []
    species = []
    for i in srange(t):
        u = minpoly[i][0]
        k = minpoly[i][1]
        nu = []
        for j in srange(0, k + 2):
            h = gcrc(f, invtau(u^j))
            nu.append(h.degree().log(r))
        m = u.degree()
        species += [[m]]
        for j in srange(1, k + 1):
            lamj = (2*nu[j] - nu[j - 1] - nu[j + 1]).divide_knowing_divisible_by(m)
            D = D + [rat_jordan_block(u, j)] *lamj
            species[-1].append(lamj)
    return [Species(lam) for lam in species] if species_only else block_diagonal_matrix(D)

def test_RJF():
    f = x^16 + (theta^2 + 1)*x
    print RJF(f)
    print RJF(f, species_only=True)





































# SECTION numL
# ============

# symbolic expression for counting formula
var('rr', 'z')
T.<rr, z> = PolynomialRing(ZZ, rr, z)

def qbracket(n, q):
    return (q^n - 1)/(q - 1)

class Species(list):
    """this is a single eigenfactor u's species lam = [deg u, lam1, lam2, ..., lamk].

    sage: lam = Species([1,0,2])
    sage: lam.deg, lam.mul, lam.dim
    (1, 2, 4)

    sage: mu = Species([1,1]); nu = Species([1,0,1]); xi = Species([1,1,1])
    sage: mu.is_subspecies(nu)
    True
    sage: xi.is_subspecies(nu)
    False
    sage: xi.is_subspecies(lam)
    True
"""

    def __init__(self, lam):
        assert len(lam) > 1
        assert lam[-1] > 0
        self.deg = lam[0]
        self.mul = len(lam) - 1
        self.orderFreq = [None] + lam[1:]
        self.dim = self.deg*sum([i*l for i, l in enumerate(lam)])

    def __repr__(self):
        return str([self.deg] + self.orderFreq[1:])

    def is_subspecies(self, other):
        '''check whether self is a subspecies of other using the criterion of Fripertinger, Theorem 3.'''
        if self.deg != other.deg:
            return False
        excess = other.mul - self.mul
        self_extend = self.orderFreq + excess*[0]
        for j in range(1, self.mul + 1):
            if sum(self_extend[j:]) > sum(other.orderFreq[j:]):
                return False
        return True

    def numMinSubspacesByDepth(self, depth):
        if depth == self.mul:
            return qbracket(self.orderFreq[depth], rr)
        return rr^sum(self.orderFreq[depth+1:])*qbracket(self.orderFreq[depth], rr)

    def quotientByDepth(self, depth):
        '''what to do if you should return 0, i.e. for input self = (deg u, 1) and depth = 1'''
        assert self.orderFreq[depth] > 0
        lam = self.orderFreq[:]
        lam[depth] -= 1
        if depth > 1:
            lam[depth - 1] += 1
        if lam[-1] == 0:
            lam = lam[:-1]
        if len(lam) == 1:
            return None
        lam[0] = self.deg
        return Species(lam)

class SpeciesCollection(Counter):
    """better: multi-set"""
    pass

def rm_trailing_zeroes(lam):
    return [a for i, a in enumerate(lam) if sum(lam[i:]) > 0]

def SubSpecies(lam, d):
    '''return list of eigenvalue species that are
    - a subspecies of lam and
    - have dimension d

TODO turn this into an iterator
    '''
    MAX = lam.dim
    all_tails = product(srange(MAX+1), repeat=lam.mul)
    temp = []
    for tail in all_tails:
        tail = rm_trailing_zeroes(tail)
        if sum(tail) == 0:
            continue
        mu = Species([lam.deg] + list(tail))
        if mu.dim == d and mu.is_subspecies(lam):
            temp.append(mu)
    return temp

def alpha(t, lam):
    '''
Fripertinger Lemma 5
species lam = [deg u, lam1, lam2, ..., lamk]
number of vectors of height t

sage: alpha(1, [2,1])    # J_u^(1) for irreducible u of degree 2
r^2 - 1                       # really? really! -- because height is dim/deg

sage: alpha(1, [1,1])    # (a)
r - 1

sage: alpha(1, [1,2])    # diag(a, a)
r^2 - _

sage: alpha(1, [1,0,1])  # matrix([[a, 1], [0, a]]) = J_a^(2)
r - 1
sage: alpha(2, [1,0,1])
r^2 - r

'''
    assert t > 0    # alternatively, return 1 (namely the 0 vector)
    Q = rr^lam.deg
    nu = sum(lam.orderFreq[t:])    # l_t
    alpha = prod([Q^(i*lam.orderFreq[i]) for i in range(1,t)])
    alpha *= (Q^t - Q^(t-1))/(Q - 1)
    alpha *= Q^((t-1)*(nu-1))*(Q^nu - 1)
    return alpha

def beta(t, lam, nu):
    '''
Fripertinger Lemma 6
vectorspace V with single eigenvalue species lam and subvectorspace U with single eigenvalue species nu

count number of vectors not in U and of height exactly t

sage: beta(1, [1,2], [1,2])
0
sage: beta(1, [1,2], [1,1])
r^2 - r
'''
    assert nu.is_subspecies(lam)
    assert t > 0    # alternatively, return 1 (namely the 0 vector)
    Q = rr^lam.deg
    k = lam.mul     # maximal size of Jordan blocks
    nuext = nu.orderFreq + (lam.mul - nu.mul)*[0]
    cofactor = Q^((t-1)*sum([lam.orderFreq[i]-nuext[i] for i in range(t, k+1)]))
    cofactor *= prod([Q^(i*lam.orderFreq[i]) for i in range(1, t)])
    return alpha(t, lam) - alpha(t, nu)*cofactor

def gamma(lam, mu):
    '''return number of bases -- sorted by non-increasing height -- for a mu-species subspace in a lam-species ambient space.

sage: gamma([1,1],[1,1])
r - 1
sage: gamma([1,2],[1,1])
r^2 - 1
'''
    assert mu.is_subspecies(lam)
    k1 = mu.mul
    nu1 = Species([mu.deg] + (mu.mul-1)*[0] + [1])
    s = sum(mu.orderFreq[1:])    # number of rational Jordan blocks
    k = k1
    kseq = [None, k1]
    nu = nu1
    nuseq = [None, nu1]
    for i in range(1, s):
        knext = max([i for i in range(mu.mul + 1) if mu.orderFreq[i] > nu.orderFreq[i]])
        kseq.append(knext)
        nuorder = nu.orderFreq[:]
        nuorder[knext] += 1
        nunext = Species([mu.deg] + nuorder[1:])
        nuseq.append(nunext)
        nu = nunext
    temp = alpha(k1, lam)
    for i in range(1, s):
        temp *= beta(kseq[i+1], lam, nuseq[i])
    return temp

def primarygf(lam):
    '''Fripertinger Theorem 2:

given the species lam of an operator A on an Fr-vectorspace, return the number of d-dimensional A-invariant Fr-subvectorspaces.

    assume for the moment that we deal with the a single eigenfactor, i.e. lam = [d, lam1, ..., lamk]

TODO: primarygf([2,4]) != primarygf([1,4]) o z^2 ?!
    '''
    return T(1 + sum(sum([gamma(lam, mu)/gamma(mu, mu) for mu in SubSpecies(lam, d)])*z^d for d in srange(1, lam.dim+1)))

def genfun(LAM):
    return prod(primarygf(lam) for lam in LAM)

def Lin(LAM, d):
    '''
    sage: Lin([2,4],1)
    0
    sage: Lin([2,4],2)
    rr^6 + rr^4 + rr^2 + 1
    sage: Lin([2,4],3)
    0
    sage: Lin([2,4],4)
    rr^8 + rr^6 + 2*rr^4 + rr^2 + 1
    '''
    return genfun(LAM).coefficient(z^d)

def test_numL():
    lam = Species([1,3])
    LAM = [lam]
    print Lin(LAM, 1)
    # rr^2 + rr + 1
    print Lin(LAM, 2)
    # rr^2 + rr + 1
























# SECTION chains
# ==============

def num_chains(lam):
    """
    LAM = [lam, mu, ...]

    lam = Species([1, 2])
    spread(lam)
    [2]_r
    lam = Species([1, 1, 1])
    spread(lam)
    2*[2]_r - 1

    lam = [1, 1]
    spread(lam)
    1
    lam = [1, 0, 1]
    spread(lam)
    1
    lam = [1, 0, 0, 1]
    spread(lam)
    1
    """
    pass

def primary_num_chains(lam):
    # base case: single block
    if sum(lam.orderFreq[1:]) == 1:
        return 1
    # base case: several blocks of size 1
    if lam.mul == 1:
        return prod([qbracket(i, rr) for i in range(1, lam.orderFreq[1] + 1)])
    tmp = 0
    for depth in range(1, lam.mul+1):
        num = lam.numMinSubspacesByDepth(depth)
        if num == 0:
            continue
        rem = lam.quotientByDepth(depth)
        tmp += num*primary_num_chains(rem)
    return tmp

def num_chains(LAM):
    if len(LAM) == 1:
        return primary_num_chains(LAM[0])
# return sum([for lam in LAM])
    tmp = 0
    for i, lam in enumerate(LAM):
        for depth in range(1, lam.mul+1):
            num = lam.numMinSubspacesByDepth(depth)
            if num == 0:
                continue
            rem = lam.quotientByDepth(depth)
            if rem == None:
                reducedLAM = LAM[:i] + LAM[i+1:]
            else:
                reducedLAM = LAM[:i] + [lam.quotientByDepth(depth)] + LAM[i+1:]
            tmp += lam.numMinSubspacesByDepth(depth)*num_chains(reducedLAM)
    return tmp

def test_num_chains():
    lam = Species([1,1,1])
    mu = Species([1,0,1])
    nu = Species([1,1])
    xi = Species([1,2])
    print num_chains([lam])    # 2r+1
    print num_chains([mu, nu]) # 3
    print num_chains([xi,nu])  # 3r+3















# SECTION Application to coding theory
# ====================================

#   \cite{bouulm14} build self-dual codes from factorizations of
#   $x^{r^{n}}-ax$ beating previously known minimal distances. Over
#   $\FF_{4}[x; 2]$, they exhibit $3$, $15$, $90$, $543$ complete
#   decompositions for $x^{2^{2}}+x$, $x^{2^{4}}+x$, $x^{2^{6}}+x$, and
#   $x^{2^{8}}+x$, respectivel.y

p = 2
e = 1
r = p^e
d = 2
q = r^d    # @future: p^d
assert p.is_prime()
assert r.is_power_of(p)
assert q.is_power_of(r)
var('eta', 'theta')
Fr = GF(r, conway=True, prefix='z')    # ground field ...
eta = Fr.gen()                         # ... and its generator
Fq = GF(q, conway=True, prefix='z')    # field extension ...
theta = Fq.gen()                       # ... and its generator
var('x, y')
# no way to restrict to the additives Fq[x; r], so we consider the whole ring R = Fq[x]
R.<x> = PolynomialRing(Fq, x)
# the centre of Fq[x; r] is Fr[x; q] with commutative image S = Fr[y]
S.<y> = PolynomialRing(Fr, y)

def test_example():
    for f in [x^4 + x, x^16 + x, x^64 + x, x^256 + x]:
        LAM = RJF(f, species_only=True)
        print LAM, num_chains(LAM).substitute(rr=r) # 3, 15, 90, 543



'''
A case by hand for reference:
p = r = 2
q = 4
F4 = [0, 1, a, a^{-1}]
sigma : a -> a^2 = a^{-1}

For ease of notation, we write a' = a^{-1} = a^2

(mini-)addition table
1 + a = a'
1 + a' = a
a + a' = 1

squarefree at degree 1: 3 polynomials (none of them central)
x + 1
x + a
x + a'

(skew-)multiplication table for degree 1 elements
      | x + 1            x + a           x + a'
------+------------------------------------------------
x + 1 | x^2 + 1          x^2 + ax + a    x^2 + a'x + a'
x + a | x^2 + a'x + a    x^2 + x + a'    x^2 + 1
x + a'| x^2 + ax + a'    x^2 + 1         x^2 + x + a

factorization of squarefree at degree 2: 12 polynomials (only the first is central)

x^2       + 1  = (x + 1)^2 = (x + a)(x + a') = (x + a')(x + a)
x^2 + x   + 1
x^2 + ax  + 1
x^2 + a'x + 1
x^2       + a
x^2 + x   + a  = (x + a')^2
x^2 + ax  + a  = (x + 1)(x + a)
x^2 + a'x + a  = (x + a)(x + 1)
x^2       + a'
x^2 + x   + a' = (x + a)^2
x^2 + ax  + a' = (x + a')(x + 1)
x^2 + a'x + a' = (x + 1)(x + a')

(skew-)multiplication table for degree-2/degree-1 and degree-1/degree-2

               | x + 1                    x + a                   x + a'
---------------+------------------------------------------------------------------------
x^2       + 1  | x^3 + x^2 + x + 1        x^3 + ax^2 + x + a      x^3 + a'x^2 + x + a'
x^2 + x   + 1  | x^3           + 1        x^3 + a'x^2 + ax + a    x^3 + ax^2 + a'x + a'
x^2 + ax  + 1  | x^3 + a'x^2 + a'x + 1    x^3 + a                 x^3 + x^3 + ax + a'
x^2 + a'x + 1  | x^3 + ax^2 + ax + 1      x^3 + x^2 + a'x + a     x^3 + a'
x^2       + a  | x^3 + x^2 + ax + a       x^3 + ax^2 + ax + a'    x^3 + a'x^2 + ax + 1
x^2 + x   + a  | x^3 + a'x + a            x^3 +a'x^2 + x + a'     x^3 + ax^2 + 1
x^2 + ax  + a  | x^3 + a'x^2 + a          x^3 + a'x + a'          x^3 + x^2 + x + 1
x^2 + a'x + a  | x^3 + ax^2 + x + a       x^3 + x^2 + a'          x^3 + a'x + 1
x^2       + a' | x^3 + x^2 + a'x + a'     x^3 + ax^2 + a'x + 1    x^3 + a'x^2 + a'x + a
x^2 + x   + a' | x^3 + ax + a'            x^3 + a'x^2 + 1         x^3 + ax^2 + x + a
x^2 + ax  + a' | x^3 + a'x^2 + x + a'     x^3 + ax + 1            x^3 + x^2 + a
x^2 + a'x + a' | x^3 + ax^2 + a'          x^3 + x^2 + x + 1       x^3 + ax + a

x + 1                   x + a                     x + a'                |
------------------------------------------------------------------------+---------------
x^3 + x^2 + x + 1       x^3 + ax^2 + x + a        x^3 + a'x^2 + x + a'  | x^2       + 1
x^3 + 1                 x^3 + a'x^2 + a'x + a     x^3 + ax^2 + ax + a'  | x^2 + x   + 1
x^3 + ax^2 + a'x + 1    x^3 + x^3 + ax + a        x^3 + a'              | x^2 + ax  + 1
x^3 + a'x^2 + ax + 1    x^3 + a                   x^3 + x^2 + a'x + a'  | x^2 + a'x + 1
x^3 + x^2 + a'x + a     x^3 + ax^2 + a'x + a'     x^3 + a'x^2 + a'x + 1 | x^2       + a
x^3 + ax + a            x^3 + a'x^2 + x + a'      x^3 + ax^2 + 1        | x^2 + x   + a
x^3 + ax^2 + x + a      x^3 + x^2 + a'            x^3 + ax + 1          | x^2 + ax  + a
x^3 + a'x^2 + a         x^3 + ax + a'             x^3 + x^2 + x + 1     | x^2 + a'x + a
x^3 + x^2 + ax + a'     x^3 + ax^2 + ax + 1       x^3 + a'x^2 + ax + a  | x^2       + a'
x^3 + a'x + a'          x^3 + a'x^2 + 1           x^3 + ax^2 + x + a    | x^2 + x   + a'
x^3 + ax^2 + a'         x^3 + x^2 + x + 1         x^3 + a'x + a         | x^2 + ax  + a'
x^3 + a'x^2 + x + a'    x^3 + a'x + 1             x^3 + x^2 + a         | x^2 + a'x + a'

factorization of squarefree at degree 3: 48 polynomials

x^3               + 1  | = (x^2 + x + 1)(x + 1) = (x + 1)(x^2 + x + 1)
x^3               + a  | = (x^2 + ax + 1)(x + a) = (x + a)(x^2 + a'x + 1)
x^3               + a' | = (x^2 + a'x + 1)(x + a') = (x + a')(x^2 + ax + 1)
x^3         +   x + 1  |
x^3         +   x + a  |
x^3         +   x + a' |
x^3         +  ax + 1  | = (x^2 + ax + a')(x + a) = (x + a')(x^2 + ax + a)
x^3         +  ax + a  | = (x^2 + a'x + a')(x + a') = (x + 1)(x^2 + x + a)
x^3         +  ax + a' | = (x^2 + x + a')(x + 1) = (x + a)(x^2 + a'x + a)
x^3         + a'x + 1  | = (x^2 + a'x + a)(x + a') = (x + a)(x^2 + a'x + a')
x^3         + a'x + a  | = (x^2 + x + a)(x + 1) = (x + a')(x^2 + ax + a')
x^3         + a'x + a' | = (x^2 + ax + a)(x + a) = (x + 1)(x^2 + x + a')
                       |
x^3 +   x^2       + 1  |
x^3 +   x^2       + a  | = (x^2 + ax + a')(x + a') = (x + a')(x^2 + a'x + a')
x^3 +   x^2       + a' | = (x^2 + a'x + a)(x + a) = (x + a)(x^2 + ax + a)
x^3 +   x^2 +   x + 1  | = (x^2 + 1)(x + 1) = (x^2 + ax + a)(x + a') = (x^2 + a'x + a')(x + a) = (x + 1)(x^2 + 1) = (x + a')(x^2 + a'x + a) = (x + a)(x^2 + ax + a')
x^3 +   x^2 +   x + a  |
x^3 +   x^2 +   x + a' |
x^3 +   x^2 +  ax + 1  |
x^3 +   x^2 +  ax + a  | = (x^2 + a)(x + 1) = (x + a)(x^2 + x + 1)
x^3 +   x^2 +  ax + a' | = (x^2 + ax + 1)(x + a') = (x + 1)(x^2 + a')
x^3 +   x^2 + a'x + 1  |
x^3 +   x^2 + a'x + a  | = (x^2 + a'x + 1)(x + a) = (x + 1)(x^2 + a)
x^3 +   x^2 + a'x + a' | = (x^2 + a')(x + 1) = (x + a')(x^2 + a'x + 1)
                       |
x^3 +  ax^2       + 1  | = (x^2 + x + a)(x + a') = (x + a')(x^2 + x + a)
x^3 +  ax^2       + a  |
x^3 +  ax^2       + a' | = (x^2 + a'x + a')(x + 1) = (x + 1)(x^2 + ax + a')
x^3 +  ax^2 +   x + 1  |
x^3 +  ax^2 +   x + a  | = (x^2 + 1)(x + a) = (x^2 + a'x + a)(x + 1) = (x^2 + x + a')(x + a') = (x + a)(x^2 + 1) = (x + 1)(x^2 + ax + a) = (x + a')(x^2 + x + a')
x^3 +  ax^2 +   x + a' |
x^3 +  ax^2 +  ax + 1  | = (x^2 + a'x + 1)(x + 1) = (x + a)(x^2 + a')
x^3 +  ax^2 +  ax + a  |
x^3 +  ax^2 +  ax + a' | = (x^2 + a)(x + a) = (x + a')(x^2 + x + 1)
x^3 +  ax^2 + a'x + 1  | = (x^2 + a')(x + a) = (x + 1)(x^2 + ax + 1)
x^3 +  ax^2 + a'x + a  |
x^3 +  ax^2 + a'x + a' | = (x^2 + x + 1)(x + a') = (x + a)(x^2 + a)
                       |
x^3 + a'x^2       + 1  | = (x^2 + x + a')(x + a) = (x + a)(x^2 + x + a')
x^3 + a'x^2       + a  | = (x^2 + ax + a)(x + 1) = (x + 1)(x^2 + a'x + a)
x^3 + a'x^2       + a' |
x^3 + a'x^2 +   x + 1  |
x^3 + a'x^2 +   x + a  |
x^3 + a'x^2 +   x + a' | = (x^2 + 1)(x + a') = (x^2 + x + a)(x + a) = (x^2 + ax + a')(x + 1) = (x + a')(x^2 + 1) = (x + a)(x^2 + x + a) = (x + 1)(x^2 + a'x + a')
x^3 + a'x^2 +  ax + 1  | = (x^2 + a)(x + a') = (x + 1)(x^2 + a'x + 1)
x^3 + a'x^2 +  ax + a  | = (x^2 + x + 1)(x + a) = (x + a')(x^2 + a')
x^3 + a'x^2 +  ax + a' |
x^3 + a'x^2 + a'x + 1  | = (x^2 + ax + 1)(x + 1) = (x + a')(x^2 + a)
x^3 + a'x^2 + a'x + a  | = (x^2 + a')(x + a') = (x + a)(x^2 + x + 1)
x^3 + a'x^2 + a'x + a' |

'''
