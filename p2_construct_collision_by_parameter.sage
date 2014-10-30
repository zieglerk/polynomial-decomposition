'''
- generate collisions by explicit constructions
- compare to the sets and counts obtained by brute force composing
- make a conjecture test: all polys are of the described form
'''

load '~/1--cdesk/programs/research/coll/compose_by_brute_force.sage'

def poly_to_para(f):
    '''returns the likely parameters eps, u, m, s, w for a composition f'''
    deg2 = (f.truncate(r^2)).degree()
    if r.divides(deg2):
        eps = 1
        ell = (r^2 - deg2)/r
    else: 
        eps = 0
        ell = (r^2 - deg2)/(r+1)
    m = (r-1)/ell
    for w_prime in K:
        F = f(x-w_prime)+f(w_prime)
        if F.coeffs()[r^2-ell*r-ell-1] == 0:
            w = w_prime
            break
    f = f(x-w)+f(w)
    if eps == 1:
        s = - f.coeffs()[r^2-ell*r-ell]/f.coeffs()[r^2-ell*r]
        u = f.coeffs()[r^2-ell*r-ell]/(K(m)*s^(r+1))
    else:
        u = -1
        s = (f.coeffs()[r^2-ell*r-ell]/(-K(m))).nth_root(r+1)
    return eps, u, m, s, w

def para_to_poly(eps, u, m, s, w):
    '''returns the polynomial f according to our construction'''
    ell = (r-1)/m
    f = x*(x^(ell*(r+1)) - eps*u*s^r*x^ell + u*s^(r+1))^m
    f = f(x+w)-f(w)
    return f
    '''
    include this, if you want the decompositions, too
    F = {}
    F[f] = []
    T = (x^(r+1)-eps*u*x+u).roots()
    for root in T:
        t = root[0]
        g = x*(x^ell - u * s^r*t^(-1))^m
        g = g(x+w)-g(w)
        h = x*(x^ell - s*t)^m
        h = h(x+w)-h(w)
        F[f].append([g,h])
    return F
    '''

# test

def check_for_non_constructed(Q):
    '''check all elements in a set of compositions for ones which do not arise from explicit construction.  CAVE: this makes only sense for sets of at least 2-collisions which are also non-Frobenii'''
    init(Q)
    C = load('data/C%s'%Q)
    A1, A2, Ar1, Frob = sort_comp_sans_Frob(C)
    warning = 0
    for f in A2:
        para = poly_to_para(f)
        if f<>para_to_poly(para[0], para[1], para[2], para[3], para[4]):
            print 'Warning: non-constructed collision found:', f
            warning += 1
    for f in Ar1:
        para = poly_to_para(f)
        if f<>para_to_poly(para[0], para[1], para[2], para[3], para[4]):
            print 'Warning: non-constructed collision found:', f
            warning += 1            
    return warning

def vvor(s, i, j):
    if mod(i-j, 2) == 1:
        return binomial(i, j+1)*s^(i-j-1)
    else:
        return 0
    
        
def proj_constructions_0(Q):
    init(Q)
    L = {}
    for b in K_units:
        T = (x^(r+1)+b).roots()    
        for u in K_units:
            for i in range(1,p):
                for root in T:
                    t = root[0]
                    s = u*t
                    v = 0
                    for j in range(0,i):
                        v += vvor(s, i, j)*x^j
                    g = x^i*(x+s)^(p-i)             
                    h = x*v*(x-s)^(p-i)
                    f = g.subs({x:h})
                    if f in L:
                        if not [g,h] in L[f]:
                            L[f].append([g,h])
                    else:
                        L[f]=[[g,h]]
    return L

def proj_constructions_1(Q):
    init(Q)
    L = {}
    for b in K:
        T = (x^(p+1)-b*x+b).roots()
        if len(T)<2:
            continue
        for s in K_units:
            t1 = s*T[0][0]
            t2 = s*T[1][0]
            v2 = (x^3 * t2 + t1 * (x-t1-t2)^3)/((t1+t2)*(x-t2))
            v1 = (v2*(x-t2)*(x-t1-t2)^2+t1)*x^(-3)
            g1 = x^2*(x-t1)^3
            h1 = x^3*v1
            g2 = x^3*(x-t2)^2
            h2 = x^2*(x-t2)*v2
            f1 = g1.subs({x:h1})
            f2 = g2.subs({x:h2})
            if f1<>f2:
                print 'Warning: no collision for ', b, t1, t2
            else:
                f = f1
                if f in L:
                    L[f].append([g1,h1], [g2, h2])
                else:
                    L[f]=[[g1,h1], [g2, h2]]
    return L

'''test a multiply original collision for twistability'''
'''Note: not all can be transformed to twisted poly's but this occurs for the first time at p=13'''

def suitable_for_modifying_twists(p):
    F = FiniteField(p)
    R = PolynomialRing(F,x)
    warning = 0
    for l in range(1,(p-1)/2):
        m = p-l
        for a in F:
            a_star = 1-a
            q = x^l + a*((x+1)^l-x^l)
            q = R(q)
            q_star = x^m + a_star*((x+1)^m-x^m)
            q_star = R(q_star)
            if not 0 in [q(b) for b in F] and not 0 in [q_star(b) for b in F]:
                print 'Warning, the following parameters (p, l, m, a, a_star) yield an unmodifiable twist', p, l, m, a, a_star 
                warning = 1
    if warning == 0:
        print 'No problems encountered, all parameters admissable for p =', p
