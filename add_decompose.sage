# related packages:
# - Maple's with(oretools) :: TODO
# - RISC's ore_algebra :: use delta = 0 and sigma = r-th power; fails since only prime fields allowed

'''
For a *single* additive polynomial, we answer two questions.
(Q1) How many right components of a given exponent exist?
(Q2) How many complete decompositions exist?

Approach
0. assume monic squarefree
1. compute RationalJordanForm (and its species) a la GathenGiesbrechtZiegler
2. use Fripertinger on species to return
   a) generating function for subspace numbers answering (i)
   b) number of chains in subspace lattice answering (ii)
3. reduce general case to assumptions in 0.

Language/design options:
1. use "skew multiplication language"
2. use "additive composition language"
We opt for 2. in the interest of compatibility with the other packages in the module.

'''

import itertools

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
    coefficients = f.coeffs()
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
    coefficients = F.coeffs()
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
    '''for a list of additive polynomials form Fq[x; r] return a list of elements of coeffients from Fr (!) such that their scalar product is zero; return None if none exists.

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
    for head in itertools.product(Fr, repeat=m - 1):
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
    return species if species_only else block_diagonal_matrix(D)







# Regarding "(Q1) How many right components of a given exponent exist?"

# symbolic expression for counting formula
var('rr', 'z')
T.<rr, z> = PolynomialRing(ZZ, rr, z)

# formatting is eigenvalue species lam = [m, lamj's],
# operator species LAM = [mu, lam, ...]

def is_subspecies(mu, lam):
    '''check if mu is a subspecies of the (eigenvalue) species lam. Using the criterion of Fripertinger, Theorem 3.

sage: is_subspecies([1,1],[1,0,1])
True
sage: is_subspecies([1,1,1],[1,0,1])
False
sage: is_subspecies([1,1,1],[1,0,2])
True
'''
    assert lam[0] == mu[0]
    muext = mu + (len(lam)-len(mu))*[0]
    k = len(lam) - 1
    for j in range(1, k+1):
        if sum(muext[j:]) > sum(lam[j:]):
            return False
        return True

def dim(lam):
    '''given an eigenvalue species lam returns the dimension of the ambient space.'''
    return lam[0]*sum([i*lam[i] for i in range(1, len(lam))])

def SubSpecies(lam, d):
    '''return all possible eigenvalue species of d-dim invariant subspaces of a vectorspace with single eigenvalue of species lam.

TODO turn this into an iterator
    '''
    if not (lam[0]).divides(d):
        return []
    MAX = dim(lam)
    all_tails = itertools.product(srange(MAX+1), repeat=len(lam)-1)
    temp = []
    for tail in all_tails:
        mu = [lam[0]] + list(tail)
        if is_subspecies(mu, lam) and dim(mu) == d:
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
    m = lam[0]
    Q = rr^m
    nu = sum(lam[t:])    # l_t
    alpha = prod([Q^(i*lam[i]) for i in range(1,t)])
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
    assert is_subspecies(nu, lam)
    assert t > 0    # alternatively, return 1 (namely the 0 vector)
    m = lam[0]
    Q = rr^m
    k = len(lam) - 1    # maximal size of Jordan blocks
    nuext = nu+(len(lam)-len(nu))*[0]
    cofactor = Q^((t-1)*sum([lam[i]-nuext[i] for i in range(t, k+1)]))*prod([Q^(i*lam[i]) for i in range(1, t)])
    return alpha(t, lam) - alpha(t, nu)*cofactor

def gamma(lam, mu):
    '''return number of bases -- sorted by non-increasing height -- for a mu-species subspace in a lam-species ambient space.

sage: gamma([1,1],[1,1])
r - 1
sage: gamma([1,2],[1,1])
r^2 - 1
'''
    assert is_subspecies(mu, lam)
    nu = [mu[0]] + (len(mu) - 1)*[0]
    s = sum(mu[1:])    # number of rational Jordan blocks
    k = max([i for i in range(len(mu)) if mu[i] > nu[i]])
    temp = alpha(k, lam)
    nu[k] += 1    # nu1
    for i in range(1, s):
        knext = max([i for i in range(len(mu)) if mu[i] > nu[i]])
        temp *= beta(knext, lam, nu)
        nu[knext] += 1
    return temp

def primarygf(lam):
    '''Fripertinger Theorem 2:

given the species lam of an operator A on an Fr-vectorspace, return the number of d-dimensional A-invariant Fr-subvectorspaces.

    assume for the moment that we deal with the a single eigenfactor, i.e. lam = [d, lam1, ..., lamk]

sage: Lin([2,4],1)
0
sage: Lin([2,4],2)
rr^6 + rr^4 + rr^2 + 1
sage: Lin([2,4],3)
0
sage: Lin([2,4],4)
rr^8 + rr^6 + 2*rr^4 + rr^2 + 1

TODO: primarygf([2,4]) != primarygf([1,4]) o z^2 ?!
'''
    return T(1 + sum(sum([gamma(lam, mu)/gamma(mu, mu) for mu in SubSpecies(lam, d)])*z^d for d in srange(1, dim(lam)+1)))


def gf(LAM):
    return prod(primarygf(lam) for lam in LAM)

def Lin(LAM, d):
    return gf(LAM).coefficient(z^d)

F = y+3*eta
G = y+eta^2+2*eta
f = invtau(F)
g = invtau(G)
print "Two central polynomials", f, g
print "and their grcrc", gcrc(f, g)

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



# WORKINGMARK



















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

'''
APPENDIX: Is r^n - 1 the maximal splitting degree for an additive polynomial of degree r^n?

def split_degree(f):
    K = f.splitting_field('Theta')
    return K.degree()/Fq.degree()

p=q=r=2
- n=15 :: r^n - 1 (over 1000 random choices)
- n=20 :: PARI OutOfMemory

q=r=4
- n=10 :: RUNNING

Max = 0
for i in range(1000):
    f = random_additive(n)
    d = split_degree(f)
    Max = max(Max, d)

print 'At degree', r^n, 'we find (after 1000 trials) as largest extension degree for the splitting field of an additive polynomial', Max
'''
