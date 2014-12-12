'''This module offers conuting functions for the decomposition of additive polynomials.

For a given additive polynomial f of degree r^n, we ask for the number of right components of f that have degree r^d. The possible numbers follow a pattern that allow only for a selected few values. For example, for additive polynomials of degree r^2, we may only have 0, 1, 2, or r+1 right components of degree r.

So, we also ask the "inverse" question: For a given $k$, how many additive polynomials of degree r^n have exactly k right components of degree r^d.

The first question is answered using the rational Jordan form of the Frobenius operator on the root space of f. The second question is motivated by our leitmotif to count the number of decomposable additive polynomials. The corresponding inclusion-exclusion formula requires counting these k-collisions.

- functions to compute the numbers as given in our papers by their explicit formula
- also including functions to deal with Bluher's equation
- make a conjecture test: the computed number is correct

datastructure: 4-tupel of cardinalities:

call this tuple coll_card(q)

variables:
- size of ground field: q
- characteristic: p
- degree of right component: r
'''

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




def coll_card(q):
    '''given the cardinality q of the ground field, this returns a four tuple of set cardinalities: subset of non-decomposable, max 1-collisions, max 2-collisions, and max r+1-collisions of polynomials over that ground field at degree p^2'''
    p = q.radical()
    r = p
    N = [0]*4
    N[-1] = simply_orig_non_Frob_card(q)[-1]
    N[2] = Frob_card(q)[2] + simply_orig_non_Frob_card(q)[2] + multiply_non_Frob_card(q)[2]
    N[1] = q^(2*(r-1))-2*N[2]-(r+1)*N[-1]
    N[0] = q^(r^2-1)-sum(N)
    return N

def Frob_card(q):
    '''Frobenius collisions may be max 1- or 2-collisions.'''
    F = [0]*4
    p = q.radical()
    F[1] = 1
    F[2] = q^(p-1)-1
    return F

def add_card(q):
    '''Same as coll_card with the restriction to only consider additive polynomials.  Given by Theorm 5.1 of gatgie09.
Note:  Sums up to q^2 and therefore includes Frobenius, where applicable'''
    A = [0]*4
    p = q.radical()
    r = p
    A[0] = r*(q^2-1)/(2*(r+1))
    A[1] = (q^2-q+r)/r
    A[2] = (q-1)*(q*(r-2)+r)/(2*(r-1))
    A[-1] = (q-1)*(q-r)/(r*(r^2-1))
    return A

def simply_orig_non_Frob_card(q):
    '''simply original, non-Frobenius collisions may be max 2- or r+1-collisions.  For consistency with coll_card and add_card, we return a list of 4 values with the first two being 0.'''
    S = [0]*4
    p = q.radical()
    r = p
    d = len(divisors(r-1))
    gamma = gcd(r+1, q-1)
    N = q*d-q+1
    A = add_card(q)
    for i in [2, -1]:
        if i == 2:
            delta = kronecker_delta(gamma,2)
            S[i] = N * (bluher_count(q,r,2) + delta*(q-1)/gamma)
        else:
            delta = kronecker_delta(gamma,r+1)
            S[i] = N * (bluher_count(q,r,r+1) + delta*(q-1)/gamma)
    return S

def multiply_non_Frob_card(q):
    '''multiply original, non-Frobenius collisions are max 2-collisions.
Note: this automatically excludes additive collisions, since multiply original, additive collisions are Frobenius'''
    M = [0]*4
    p = q.radical()
    r = p
    if p<5:
        return M
    M[2] = (p-3)*q*(q-1)*(q-2)/4
    return M

def count_dict(C, q):
    '''given a dictionary of the form {f1: [[g11,h11],[g12,h12]], f2: ... } we want to return a 4-tuple of [0, 1, 2, r+1]-collisions'''
    N = [0]*4
    p = q.radical()
    r = p
    for f in C:
        n = len(C[f])
        if 0 < n < 3:
            N[n] += 1
        elif n == r+1:
            N[-1] += 1
        else:
            print 'Warning: non-Bluher collision', f, C[f]
    return N

def print_para_coll(C, q):
    for f in C:
        if len(C[f])>1:
            print f, para(f)

def plot_exponent_simply(Q):
    L = []
    for q in primes(3,Q):
        L.append([q, log(float(sum(simply_orig_non_Frob_card(q))), float(q))])
    print L
    G = list_plot(L)
    G.show()

def plot_for_fixed_prime(p):
    L = []
    for e in range(1, 100):
        q = p^e
        L.append([e, log(float(sum(coll_card(q)[2:3])), float(q))])
    print L
    G = list_plot(L)
    G.show()

def plot_rel_dec_for_fixed_prime(p):
    L = []
    for e in range(1, 10):
        q = p^e
        L.append([e, float( ( sum(coll_card(q)[1:]) / q^(2*p-2)  - 1 ) * q )])
    print L
    G = list_plot(L)
    G.show()

def plot_rel_dec_for_3():
    p = 3
    L = []
    for e in range(1, 100):
        q = p^e
        L.append([e, float( ( sum(coll_card(q)[1:])  - (q^4 - 3*q^3/8 - 3*q^2/8 + 3*q/8 + 3/8) ) )])
    print L
    G = list_plot(L)
    G.show()

def plot_exponent_multiply(Q):
    L = []
    for q in prime_powers(3,Q):
        L.append([q, log(float(sum(multiply_non_Frob_card(q))), float(q))])
    print L
    G = list_plot(L)
    G.show()

def epsell(C2r):
    answer = [{}, {}, {}, {}]
    for f in C2r:
        eps, ell = para(f)
        if eps == 0 and ell == r-1:
            answer[0][f] = C2r[f]
        elif eps == 0 and ell < r-1:
            answer[1][f] = C2r[f]
        elif eps == 1 and ell == r-1:
            answer[2][f] = C2r[f]
        elif eps == 1 and ell < r-1:
            answer[3][f] = C2r[f]
    return answer


def bluher_count(q,r,i):
    d = int(log(q,r))
    count = 0
    if d%2 == 0:
        if i == 2:
            count = (q-1)^2*(r-2)/(2*(r-1))
        elif i == r+1:
            count = (q-1)*(q-r^2)/(r*(r^2-1))
    elif d%2 == 1 and r%2 == 1:
        if i == 2:
            count = (q-1)*(q*r-2*q-2*r+3)/(2*(r-1)) # Note: returns 0 for q = r = 3.  And that's consistent.
        elif i == r+1:
            count = (q-1)*(q-r)/(r*(r^2-1))
    else:
        if i == 2:
            count = (q-1)^2*(r-2)/(2*(r-1))
        elif i == r+1:
            count = (q-1)*(q-r)/(r*(r^2-1))
    return count

def lower_bound(q,r,i):
    gamma = gcd(r+1, q-1)
    delta = kronecker_delta(gamma,i)
    d = len(divisors(r-1))
    e0lr1 = kronecker_delta(gamma, i)*(q-1)/gamma # epsilon = 0, ell = r-1
    e0ll = kronecker_delta(gamma, i)*(q-1)*q*(d-1)/gamma # epsilon = 0, ell < r-1
    e1lr1 = bluher_count(q,r,i) # epsilon = 1, ell = r-1
    e1ll = q*bluher_count(q,r,i)*(d-1) # epsilon = 1, ell < r-1
    return e0lr1, e0ll, e1lr1, e1ll

def para(f):
    deg2 = (f.truncate(r^2)).degree()
    if r.divides(deg2):
        eps = 1
        ell = (r^2 - deg2)/r
    else:
        eps = 0
        ell = (r^2 - deg2)/(r+1)
    return eps, ell

def main():
    global q, p, r
    global y, K, x, R, Z

    for q in range(3,4):
        if q==1 or not is_prime_power(q):
            continue
        init(q)
        D = comp(r,r)
        C = find_coll(D)
        lower_bounds = sum([sum(lower_bound(q,r,2)), sum(lower_bound(q,r,r+1)), q^(r-1)-1])
        if len(C)==lower_bounds:
            print 'overall count is fine:', lower_bounds, 'collisions'
        C2, Cr1, Frob = sort_coll(C)
        print C2, len(C2), sum(lower_bound(q,r,2))
        print Cr1, len(Cr1), sum(lower_bound(q,r,r+1))
        print Frob, len(Frob), q^(r-1)-1
        C2_para = epsell(C2)
        Cr1_para = epsell(Cr1)
        print C2_para, map(len, C2_para), lower_bound(q,r,2)
        print Cr1_para, map(len, Cr1_para), lower_bound(q,r,r+1)



'''
def GenerateCollision(eps, u, ell, s, w):
    global q, p, r
    global y, K, x, R, Z

    F = {}
    m = (r-1)/ell
    f = x*(x^(ell*(r+1)) - eps*u*s^r*x^ell + u*s^(r+1))^m
    print f
    f = f(x+w)-f(w)
    F[f] = []
    T = (x^(r+1)-eps*u*x+u).roots()
    print T
    for root in T:
        t = root[0]
        g = x*(x^ell - u * s^r*t^(-1))^m
        g = g(x+w)-g(w)
        h = x*(x^ell - s*t)^m
        h = h(x+w)-h(w)
        F[f].append([g,h])
    return F

print GenerateCollision(1,1,1,1,0)

def scan(B):
    for f in B:
        if diff(f,x)(0)==0:
            print f, B[f]
'''

'''
        if len(C) == sum(lower_bounds):
            print 'conjecture tested and true for q =', q
        else:
            print 'conjecture tested, but false for q =', q
            print 'lower_bounds are', lower_bounds
            print 'number of collisions are', len(C)
'''

# def compose(n):
#     print 'compositions in degree n =',n
#     for l in divisors(n):
#         m = Integer(n/l)
#         if l != 1 and m!=1:
#             time comp(l,m)
#             print (l,m), 'done'

# time compose(n)

'''

# get a list of possible multiplicities and sort them

list_of_multiplicities = list(set(Counter))
list_of_multiplicities.sort()

# write down the compopsition pattern

print 'field size q =', q, 'degree n =', n
for i in list_of_multiplicities:
    print i, Counter.count(i)
print 'total', len(F)

# BONUS FUNCTION NOW AVAILABLE

# a list of collisions of certain multiplicity

def coll(n):
    answer = []
    for f in F:
        i = F.index(f)
        if Fwithcounter[i][1] == n:
            answer.append(Fwithdecomps[i])
    return answer

# NEXT TOPIC: Classifiying compositions

# split F into two lists: one containing pure powers and the rest

PowerF = []
RestF = []
RestFwithcounter = []
RestCounter = []
RestFwithdecomps = []

powers = [Z(x^p).subs(x=q)] # mostly we want to detect the invariants under Frobenius, but we want to reserve the possibility to find other powers, too

def cleanup(F):
    for i in srange(len(F)):
#        cent = floor(len(F)/10)
#        if mod(i,cent) == 0:
#            print 'one ping of ten'
        f = F[i]
        pairs = Fwithdecomps[i][1:]
        detect = 0
        for gh in pairs:
            if gh[0] in powers:
                detect = 1
        if detect == 1:
            PowerF.append(f)
        else:
            RestF.append(f)
            RestFwithcounter.append(Fwithcounter[i])
            RestCounter.append(Fwithcounter[i][1])
            RestFwithdecomps.append(Fwithdecomps[i])

time cleanup(F)

# write down the compopsition pattern

print 'excluding p-powers'
for i in list_of_multiplicities:
    print i, RestCounter.count(i)
print 'total', len(RestF)

# BONUS FUNCTION NOW AVAILABLE

# a list of collisions of certain multiplicity where powers of the Frobenius are excluded

def restcoll(n):
    answer = []
    for f in RestF:
        i = RestF.index(f)
        if RestFwithcounter[i][1] == n:
            answer.append(RestFwithdecomps[i])
    return answer

# NEXT TOPIC: Search for twins or the like

def checkfortwins():
    for f in F:
        i = F.index(f)
        l = Fwithcounter[i][1]
# checking for equal g's
        for j in srange(l):
            g = Fwithdecomps[i][j+1][0]
            for k in srange(l):
                gstar = Fwithdecomps[i][k+1][0]
                if j <> k and g == gstar:
                    print Fwithdecomps[i], 'has a decomposition with equal gs'
# checking for equal h's
        for j in srange(l):
            h = Fwithdecomps[i][j+1][1]
            for k in srange(l):
                hstar = Fwithdecomps[i][k+1][1]
                if j <> k and h == hstar:
                    print Fwithdecomps[i], 'has a decomposition with equal hs'
s# checking for twist's
        for j in srange(l):
            g = Fwithdecomps[i][j+1][0]
            for k in srange(l):
                h = Fwithdecomps[i][k+1][1]
                if g == h:
                    print Fwithdecomps[i], 'has a decomposition with a twist'

# APPENDIX: solving Bluher

# INPUT: base field F, parameter r
# PROCESS: compute all u in C_{z+1} and the corresponding t's.
# OUTPUT:
# - UT: a list whose entries are pairs of the form [u, [t^{(0)}, t^{(1)}, ..., t^{(z)}]]
# - U: a list of u's
# - T: a list of lists of t's

# set the base field
p = 5
e = 4
q = p^e
y = var('y')
F = GF(q,y)
# set the the p-power part of deg g
d = 1
r = p^d
# find the interesting index z+1
c = gcd(d,e)
z = p^c

cardinality = floor(q/(z^3-z))

if cardinality <1:
    print 'The set is empty.'

# Generate a list of F to make the index accessible
Faslist = list(F)
# Generate a list of u's with some initial counter
Fwithcounter = []
for u in F:
    Fwithcounter.append([u,0])
# run through all possible values for t
for t in F:
    if t!=0 and t!=1:
# compute the corresponding u
        u = (t^(r+1))/(t-1)
# increase the counter of the corresponding u by 1 ...
        i = Faslist.index(u)
        Fwithcounter[i][1] += 1
# ... and attach the value for t
        Fwithcounter[i].append(t)

# Collect onlyt u's and t's where the counter is z+1
UT = []
for u in Fwithcounter:
    if u[1] == r+1:
        UT.append([u[0],u[2:]])
print UT

# extract only the u's
U = []
for u in Fwithcounter:
    if u[1] == r+1:
        U.append(u[0])
print U

# extract lists of t's
T = []
for u in Fwithcounter:
    if u[1] == r+1:
        T.append(u[2:])
print T

'''


# Bonus: Count a la CoulterHavasHenderson2004
#
# # we start with additive polynomials at degree p^2 over a field of size q
# # we restrict to monic polynomials
#
# def A(q):
#     '''total number of p-additive polynomials at degree p^2 over a field of size q; not normalized'''
#     return q^2
#
# def MoebiusSum(p,n):
#     return sum([moebius(n/d)*p^d for d in n.divisors()])/n
#
# def IOdoni(q):
#     p = q.factor()[0][0]
#     return (q^2-1)/(p^2-1) * MoebiusSum(p,2)
#
# def DOdoni(q):
#     '''decomposable p-additive polynomails at degree p^2 over a field of size q; no normalization'''
#     return A(q) - IOdoni(q)
#
# def IGGZ(q):
#     p = q.factor()[0][0]
#     return (q^2-1)/(p^2-1) * MoebiusSum(p,2)
#
# def DGGZ(q):
#     return A(q)- IGGZ(q)
#
# # now the approach by Susem's
# # we handle the additive ones (m=1) first
#
# def Suse(q):
#     '''number of Susem's at degree p^2 over a field of size q with m=1'''
#     p = q.factor()[0][0]
#     return q*(q-1)
#
# # this should be q^2, the number of additives;  I/We are probably requiring linear coefficient non-zero
#
#
# def IGGZ2(q):
#     '''number of indecomposable Susem's, where m=1;  this should be'''
#     pass
#
#
# for q in prime_powers(2,10):
#     print q, A(q), DOdoni(q), DGGZ(q)
