'''load and init'''

def simple_root_check(f):
    '''for all constants c in K, check f-c for a simple root'''
    for c in K:
        V = (f-c).roots()
        for v in V:
            if v[1] == 1:
                return 1
    return 0

def separate_good_from_bad(Q):
    init(Q)
    good = []
    bad = []
    for g_trunc in R.monics(of_degree = p-1):
        g = x * g_trunc
        if simple_root_check(g):
            good.append(g)
        else:
            bad.append(g)
    return good, bad

def comp(l,m):
    '''compute a dictionary {f1: [[g11, h11], [g12,h12]], f2: ...} containing all compositions of l- and m-degree monic original polynomials'''
    D = {}
    number_of_left_components = q^(l-1)
    counter = 0
    for g_trunc in R.monics(of_degree = l-1):
        g = x * g_trunc
        deg2g = (g.truncate(l)).degree()
        for h_trunc in R.monics(of_degree = m-1):
            h = x * h_trunc
            deg2h = (h.truncate(m)).degree()
            if deg2g <> deg2h:
                continue # do not compose g and h of different second degree, since they never yield collisions, according to Proposition ???
            if f in D:
                D[f].append([g,h])
            else:
                D[f]=[[g,h]]
        counter += 1
    return D

def sub_comp(l,m):
    '''compute a subset of the dictionary {f1: [[g11, h11], [g12,h12]], f2: ...} containing all compositions of l- and m-degree monic original polynomials'''
    D = {}
    number_of_left_components = (q-1)*(l-1)+1
    counter = 0
    deg2g = l-1
    for i in range(1,l):
        for c in K_units:
            g = x^i * (x-c)^(l-i)
            for h_trunc in R.monics(of_degree = m-1):
                h = x * h_trunc
                deg2h = (h.truncate(m)).degree()
                if deg2g <> deg2h:
                    continue # do not compose g and h of different second degree, since they never yield collisions, according to Proposition ???
                f = g.subs({x:h})
                if f in D:
                    D[f].append([g,h])
                else:
                    D[f]=[[g,h]]
            counter += 1
            print counter, ' left component(s) done. ', number_of_left_components-counter, ' remaining.'
    for g_prime in R.monics(of_degree = 2):
        g = x^3*g_prime^2
        deg2g = (g.truncate(m)).degree()
        for h_trunc in R.monics(of_degree = m-1):
            h = x * h_trunc
            deg2h = (h.truncate(m)).degree()
            if deg2g <> deg2h:
                continue # do not compose g and h of different second degree, since they never yield collisions, according to Proposition ???
            f = g.subs({x:h})
            if f in D:
                D[f].append([g,h])
            else:
                D[f]=[[g,h]]
    return D

def sort_comp(D):
    '''partition a dictionary D of compositions according to multiplicity into A1, A2, and Ar+1'''
    A1 = {} # unique decomposition
    A2 = {} # max 2-collision
    Ar1 = {} # max (r+1)-collision
    for f in D:
        if len(D[f])==1:
            A1[f] = D[f]
        elif len(D[f])==2:
            A2[f] = D[f]
        elif len(D[f])==r+1:
            Ar1[f] = D[f]
        else:
            print 'Warning! Polynomial found which is a maximal k-collision for k != 1,2,r+1:', f
    return A1, A2, Ar1

def detect_Frob(list):
    '''return 1 if the Frobenius automorphism occurs in a list of compositions, return 0 otherwise'''
    frob = R(x^r)
    indicator = 0
    for pair in list:
        if frob in pair:
            indicator = 1
    return indicator

def sort_comp_sans_Frob(D):
    '''same as sort_comp, but additionally singles out all Frobenius collisions'''
    A1 = {}
    A2 = {}
    Ar1 = {}
    Frob = {}
    D_sans_Frob = {}
    for f in D:
        if detect_Frob(D[f])==1:
            Frob[f] = D[f]
        else:
            D_sans_Frob[f] = D[f]
    A1, A2, Ar1 = sort_comp(D_sans_Frob)
    return A1, A2, Ar1, Frob

'''
as a first attempt to speed things up, we tried an integer version of the above -- hoping it would require less memory, but the time taken was worse: 0.01s, 015s, and 956.97s instead of 0.01s, 0.05s, and 258.04s for the primes 2, 3, and 5, respectively.

as a second attempt we went for a parrelel approach:  computing separate lists for each g and merging them latter.  This (repeated writing) also slowed down the whole process (0.07s, 0.13s, 373.35s for primes as above).
'''

'''
APPENDIX: symbolic composition for equations on the composition in terms of the coefficients of g and h


# 1. define the coefficient field F=GF(q)
p = 5
e = 1
q = p^e
y = var('y')
F = GF(q, 'y')
y = F.gens()[0]

# 2. create variables for the of g and h
all_var = ['x']
for i in range (1,p):
    var('g%s'%i)
all_var.extend(['g%s'%i for i in range(1,p)])
for i in range (1,p):
    var('h%s'%i)
all_var.extend(['h%s'%i for i in range(1,p)])
for i in range (1,p^2):
    var('f%s'%i)
all_var.extend(['f%s'%i for i in range(1,p^2)])
var('T, e1, e2, e3')
all_var.extend(['T', 'e1', 'e2', 'e3'])

R = PolynomialRing(F, all_var)
R.inject_variables()

g_coeff = [0]
g_coeff.extend(R.gens()[1:p])
g_coeff.append(1)

h_coeff = [0]
h_coeff.extend(R.gens()[p:2*p-1])
h_coeff.append(1)

# 3. create g, h and f

g = R(0)
h = R(0)
for i in srange(1,p+1):
    g += g_coeff[i]*x^i
    h += h_coeff[i]*x^i
g = R(g)
h = R(h)

f = g.substitute(x=h)

# 4. assume some zeroes and print the interesting coefficients

# f = f.substitute(h3 = h4^2)
# f = f.substitute(h2 = h4^3+h4*e1)
# f = f.substitute(h1 = h4^4+2*e1*h4^2+e2*h4)
# f = f.substitute(e1=0)
# f = f.substitute(e2=0)
# f = f.substitute(h4 = T)
# f = f.substitute(g4 = T^(-1))
# f = f.substitute(g3 = f15 - (2*h4^2*f19*e1 - 2*h4*f19*e2 - g4^2 + f20^2))
# f = f.expand()

for i in srange(p*(p-1), p*(p-3), -1):
    F = f.coefficient(x^i)
#    F = (F//(h4^5))*(f20-g4) + (F%(h4^5))
#    F = (F//(h4^5))*(f20-g4) + (F%(h4^5))
#    F = (F//(-g4*h4))*f19 + (F%(-g4*h4))
#    F = (F//(-g4*h4))*f19 + (F%(-g4*h4))
    print i, F

# use this to compose "with gaps"

# 5a. assume some zeroes and print the interesting coefficients, e.g. for p=5

f = f.substitute(h4 = 0)
f = f.substitute(g4 = 0)
f = f.substitute(h2 = 0)
f = f.substitute(h1 = - h3^2)
f = f.substitute(g2 = 0)
f = f.substitute(g1 = -g3^2)
# f = f.substitute(h2 = h4^3+h4*e1)
# f = f.substitute(h1 = h4^4+2*e1*h4^2+e2*h4)
# f = f.substitute(h4 = T)
# f = f.substitute(g4 = T^(-1))
# f = f.substitute(g3 = f15 - (2*h4^2*f19*e1 - 2*h4*f19*e2 - g4^2 + f20^2))
# f = f.substitute(e1=0)
# f = f.substitute(e2=0)
# f = f.expand()

for i in srange(p*(p-1), 0 , -1):
    F = f.coefficient(x^i)
#    F = (F//(h4^5))*(f20-g4) + (F%(h4^5))
#    F = (F//(h4^5))*(f20-g4) + (F%(h4^5))
#    F = (F//(-g4*h4))*f19 + (F%(-g4*h4))
#    F = (F//(-g4*h4))*f19 + (F%(-g4*h4))
    print i, F

# f = R(x^25+u*x^15-2*u*x^13-u^2*x^5-u^2*x^3-u^2*x)
f = R(x^25+1*x^15-2*1*x^13-1^2*x^5-1^2*x^3-1^2*x)

# 5b. ... or for p=7

# 4. assume some zeroes and print the interesting coefficients

f = f.substitute(h5 = h6^2)
f = f.substitute(h4 = h6^3)
f = f.substitute(h3 = h6^4)
f = f.substitute(h2 = h6^5)
f = f.substitute(h1 = h6^6)
# f = f.substitute(h4 = T)
# f = f.substitute(g4 = T^(-1))
# f = f.substitute(g3 = f15 - (2*h4^2*f19*e1 - 2*h4*f19*e2 - g4^2 + f20^2))
# f = f.substitute(e1=0)
# f = f.substitute(e2=0)
# f = f.expand()

for i in srange(p*(p-1), 0, -1):
    F = f.coefficient(x^i)
#    F = (F//(h4^5))*(f20-g4) + (F%(h4^5))
#    F = (F//(h4^5))*(f20-g4) + (F%(h4^5))
#    F = (F//(-g4*h4))*f19 + (F%(-g4*h4))
#    F = (F//(-g4*h4))*f19 + (F%(-g4*h4))
    print i, F
'''
