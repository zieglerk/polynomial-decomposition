# try this with Maple's with(oretools)
# discarded RISC's ore_algebra, since they only allow prime fields
# for reference: you should have delta = 0 and sigma = r-th power

'''

Eventually, this becomes "RationalJordanForm"

'''

def RJF(f, q, r):
    # check input assertions
    pass
    assert is_monic(f)
    assert is_squarefree(f)
    assert is_additive(f, q, r)
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

p = 2
e = 2
r = p^e
d = 1
q = r^d    # @future: p^d

assert p.is_prime()
assert r.is_power_of(p)
assert q.is_power_of(r)

var('theta')
Fq.<theta> = GF(q, theta)    # specify modulus=theta^3+theta+1 as Mark

var('x,y')
S.<y> = PolynomialRing(Fq,y)    # skew world: F(y)
R.<x> = PolynomialRing(Fq,x)    # add world: f(x); no way to restrict to r-additive ones

def skew_to_add(F):
    n = F.degree()
    f = x^(r^n)
    coefficients = F.coeffs()
    for i in srange(n):
	f += coefficients[i]*x^(r^i)
    return f

def random_additive(n):
    '''return random additive polynomial of exponent n. TODO optional: squarefree'''
    F = y^n + S.random_element(degree=n-1)    # monic skew -> monic original add
    return skew_to_add(F)

def split_degree(f):
    K = f.splitting_field('Theta')
    return K.degree()/Fq.degree()

def gcrd(f,g):
    return gcd(f,g)

def lclm(f,g):
    pass

n = 10    # exponent of polynomial to decompose
f = random_additive(n)
g = random_additive(n)

H1 = y+3*theta
H2 = y+theta^2+2*theta


Max = 0

'''
Is r^n - 1 the maximal splitting degree for an additive polynomial of degree r^n?

p=q=r=2
- n=15 :: r^n - 1 (over 1000 random choices)
- n=20 :: PARI OutOfMemory

q=r=4
- n=10 :: RUNNING

'''


for i in range(1000):
    f = random_additive(n)
    d = split_degree(f)
    Max = max(Max, d)

print 'At degree', r^n, 'we find (after 1000 trials) as largest extension degree for the splitting field of an additive polynomial', Max

print f, g
print gcrd(f,g)

print split_degree(f)
print split_degree(g)

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
