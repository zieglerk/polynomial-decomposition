# related packages:
# - Maple's with(oretools) :: TODO
# - RISC's ore_algebra :: use delta = 0 and sigma = r-th power; fails since only prime fields allowed

'''
For a *single* additive polynomial, we answer two questions.
(i) How many right components of a given exponent exist?
(ii) How many complete decompositions exist?

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

d = 2      # TODO fix coercion error if d > 1; Fq is field extension of Fr of degree d -- identify!
# Look at #11938 which is for coercion from one finite field to another. It needs a review. If you have the background, please review it. :)
q = r^d    # @future: p^d

assert p.is_prime()
assert r.is_power_of(p)
assert q.is_power_of(r)

Fr = GF(r, conway=True, prefix='z')    # smaller field
Fq = GF(q, conway=True, prefix='z')    # field extension

var('x, y')
# no way to restrict to Fq[x; r], so we consider the whole ring R = Fq[x]
R.<x> = PolynomialRing(Fq, x)
# its centre is Fr[x; q] with commutative image S = Fr[y]
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

def tau(f):
    '''maps additive polynomials in the centre Fr[x; q] of R = Fq[x; r] to their commutative image S = Fr[y]'''
    assert f in R
    f = R(f)
    assert is_central(f)
    n = f.degree().log(r)
    F = S(0)
    coefficients = f.coeffs()
    for i in srange(n+1):
        F += coefficients[r^i]*y^i
    return F

def invtau(F):
    '''inverse map of tau, taking a polynomial from S = Fr[y] and mapping it to (the centre of) R = Fq[x; r]'''
    assert F in S
    F = S(F)
    n = F.degree()
    f = R(0)
    coefficients = F.coeffs()
    for i in srange(n+1):
        f += coefficients[i]*x^(q^i)
    assert is_central(f)
    return f

def gcrc(f,g):
    return gcd(f,g)

def rdiv_with_rem(f,g):
    '''return (q, r) such that f = q o g + r and r minimal.'''
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

# MAJOR TODO
# construct mclc via division with remainder

def mclc(h):
    '''return minimal monic central f, such that f = g o h for some g.

You can then always the cofactor ''g'' via rdiv_with_rem(f,h)[0].
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
        centrals += cent
        remainders += rem
        if linear_relation(remainders):
            coeffs = linear_relation(polys)
            central = dot_product(coeffs, centrals)
            return central
    print 'Warning! No bound found in due time.'

def random_additive(n):
    '''return random monic r-additive polynomial of exponent n. TODO optional: squarefree'''
    F = y^n + S.random_element(degree=n-1)    # monic skew -> monic original add
    f = x^(r^n)
    for i in srange(n):
        f += Fq.random_element()*x^(r^i)
    assert is_additive(f)
    return f

F = y+3*eta
G = y+eta^2+2*eta
f = invtau(F)
g = invtau(G)
print f, g
print gcrc(f, g)

n = 2
f = random_additive(n)
g = random_additive(n-2)
print f, g
quo, rem = rdiv_with_rem(f,g)
print quo, rem, f == quo.subs(g) + rem









def RJF(f, q, r):
    # check input assertions
    assert is_monic(f)
    assert is_squarefree(f)
    assert is_additive(f)
    pass
    n = expn(f)
    return block_diagonal_matrix(rat_jordan_block(u1,e11), rat_jordan_block(u1,e12), ...)

def rat_jordan_block(u, e):
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










import itertools

def is_subspecies(mu, lam):
    '''check if mu is a subspecies of lam. Using the criterion of Fripertinger, Theorem 3.

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
    '''given a species returns the dimension of the ambient space.'''
    return lam[0]*sum([i*lam[i] for i in range(1, len(lam))])

def SubSpecies(lam, k):
    '''return all species of k-dim subspaces of a lambda-species vectorspace.

TODO turn ths into an iterator
    '''
    assert (lam[0]).divides(k)
    MAX = dim(lam)
    all_tails = itertools.product(srange(MAX+1), repeat=len(lam)-1)
    temp = []
    for tail in all_tails:
        mu = [lam[0]] + list(tail)
        if is_subspecies(mu, lam) and dim(mu) == k:
            temp.append(mu)
    return temp


def Frib_alpha(t, lam):
    '''
Fripertinger Lemma 5
species lam = [deg u, lam1, lam2, ..., lamk]
number of vectors of height t


sage: Frib_alpha(1, [2,1])    # J_u^(1) for irreducible u of degree 2
r^2 - 1                       # really? really! -- because height is dim/deg

sage: Frib_alpha(1, [1,1])    # (a)
r - 1

sage: Frib_alpha(1, [1,2])    # diag(a, a)
r^2 - _

sage: Frib_alpha(1, [1,0,1])  # matrix([[a, 1], [0, a]]) = J_a^(2)
r - 1
sage: Frib_alpha(2, [1,0,1])
r^2 - r

'''
    var('r')
    assert t > 0    # alternatively, return 1 (namely the 0 vector)
    m = lam[0]
    Q = r^m
    nu = sum(lam[t:])    # l_t
    alpha = prod([Q^(i*lam[i]) for i in range(1,t)])
    alpha *= (Q^t - Q^(t-1))/(Q - 1)
    alpha *= Q^((t-1)*(nu-1))*(Q^nu - 1)
    return alpha

def Frib_beta(t, lam, nu):
    '''
Fripertinger Lemma 6
vectorspace V with species lam and subvectorspace U with species nu

count number of vectors not in U and of height exactly t

sage: Frib_beta(1, [1,2], [1,2])
0
sage: Frib_beta(1, [1,2], [1,1])
r^2 - r
'''
    var('r')
    assert is_subspecies(nu, lam)
    assert t > 0    # alternatively, return 1 (namely the 0 vector)
    m = lam[0]
    Q = r^m
    k = len(lam) - 1    # maximal size of Jordan blocks
    nuext = nu+(len(lam)-len(nu))*[0]
    cofactor = Q^((t-1)*sum([lam[i]-nuext[i] for i in range(t, k+1)]))*prod([Q^(i*lam[i]) for i in
                                                                          range(1, t)])
    return Frib_alpha(t, lam) - Frib_alpha(t, nu)*cofactor



def Frib_gamma(lam, mu):
    '''return number of bases -- sorted by non-increasing height -- for a mu-species subspace in a lam-species ambient space.

sage: Frib_gamma([1,1],[1,1])
r - 1
sage: Frib_gamma([1,2],[1,1])
r^2 - 1
'''
    var('r')
    assert is_subspecies(mu, lam)
    nu = [mu[0]] + (len(mu) - 1)*[0]
    s = sum(mu[1:])    # number of rational Jordan blocks
    k = max([i for i in range(len(mu)) if mu[i] > nu[i]])
    temp = Frib_alpha(k, lam)
    nu[k] += 1    # nu1
    for i in range(1, s):
        knext = max([i for i in range(len(mu)) if mu[i] > nu[i]])
        temp *= Frib_beta(knext, lam, nu)
        nu[knext] += 1
    return temp

def numU(lam, k):
    '''Fripertinger Theorem 2:

given the species lam of an operator A on an Fr-vectorspace, return the number of k-dimensional A-invariant Fr-subvectorspaces.

    assume for the moment that we deal with the a single eigenfactor, i.e.
    '''
    return (sum([Frib_gamma(lam, mu)/Frib_gamma(mu, mu) for mu in SubSpecies(lam, k)])).simplify_full()








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
