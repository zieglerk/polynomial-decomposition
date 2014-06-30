'''
TOC
'''

q = var('q')
z = var('z')
k = var('k')
y = var('y')
z = var('z')

# 0. Dickson polynomials for table
# ================================

def dickson_T(n, original=False):
    '''
    return n-th Dickson polynomial T_n(x,z) of the first kind.

    sage: [dickson_T(n) for n in range(5)]
    [2, x, x^2 - 2*z, x^3 - 3*x*z, x^4 - 4*x^2*z + 2*z^2]

    sage: [dickson_T(k, original=True) for k in range(5)]
    [None, x, x^2, x^3 - 3*x*z, x^4 - 4*x^2*z]

    for comparison with n-th Chebyshev polynomial chebyshev_T of the first kind
    sage: for k in range(10):
    ....:     f = dickson_T(k).subs(x = 2*x*z, z = z^2)
    ....:     g = (2*z^k*chebyshev_T(k, x)).expand()
    ....:     print (f - g).is_zero()
    ....:
    True
    True
    True
    True
    True
    True
    True
    True
    True
    True
    '''
    var('x,z')    # to make them symbolic
    if n == 0:
        if original:
            return    # undefined
        return 2
    if n == 1:
        return x
    f = x^n
    for i in srange(1,n/2+1):
        f += n/(n-i) * binomial(n-i, i) * (-z)^i * x^(n-2*i)
    if original:
        f = f - f.subs(x=0)
    return f

def E(d, e, q):
    '''generator of exponential components at degree d with exponent e over Fq.'''
    assert q.is_prime_power()
    assert d >= 2 and e >= 1
    assert gcd(d, e) == 1
    assert gcd(d*e, q) == 1
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    if e == 1:
        return (f*x for f in R.monics(of_degree=d - 1))
    s = floor(d/e)
    k = d - e*s
    return [x^k*w^e for w in R.monics(of_degree=s)]

def T(d, e, q):
    '''generator for trigonometric components at degree d with exponent e over Fq.'''
    assert q.is_prime_power()
    assert d >= 2 and e >= 1
    assert gcd(d, e) == 1
    assert gcd(d*e, q) == 1
    T = dickson_T(d)
    R.<x,z> = PolynomialRing(GF(q, 'y'), 'x', 'z')
    T = R(T)
    F = R.base_ring()
    return (T.subs({z: y^e}) for y in F if y != 0)

'''
'''

def inter(d,e,q):
    '''
    Check lem:12:iii: E(d,e,q)^Fq \cap T(d,e,q)^Fq = 0
    '''
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    F = R.base_ring()
    E0 = E(d, e, q)
    Eorbit = [f(x+a)-f(a) for f in E0 for a in F]
    # return Eorbit
    T0 = T(d, e, q)
    # return [f for f in T0]
    T0 = [R(f) for f in T0]
    # return T0
    Torbit = [f(x+a)-f(a) for f in T0 for a in F]
    return [f for f in Eorbit if f in Torbit]

def orbT(d,e,q):
    '''
    Check pro:6:i: # T(d,e,q)^Fq = q       for d = 2
                                   q*(q-1) for d > 2
    '''
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    F = R.base_ring()
    T0 = T(d, e, q)
    T0 = [R(f) for f in T0]
    Torbit = [f(x+a)-f(a) for f in T0 for a in F]
    if d == 2:
        return len(Set(Torbit)) - q
    return len(Set(Torbit)) - q*((q-1)/gcd(q-1,e))

def orbE(d,e,q):
    '''
    Check pro:6:ii: # E(d,e,q)^Fq = q^(d-1)                   for e=1
                                    q^(floor(d/2)+1)-q(q-1)/2 for e=2
                                    q^(floor(d/e)+1)          for e>2
    '''
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    F = R.base_ring()
    E0 = E(d, e, q)
    E0 = [R(f) for f in E0]
    Eorbit = [f(x+a) - f(a) for f in E0 for a in F]
    if e == 1:
        return len(Set(Eorbit)) - q^(d-1)
    if e == 2:
        return len(Set(Eorbit)) - (q^(floor(d/2) + 1) - q*(q - 1)/2)
    return len(Set(Eorbit)) - q^(floor(d/e) + 1)

def collE(d,e,q):
    '''return collision of parameters for shifted exponential polynomials with e=2.'''
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    F = R.base_ring()
    E0 = E(d, e, q)
    E0 = [R(f) for f in E0]
    for f in E0:
        for a in F:
            fshift = f(x+a) - f(a)
            if a != 0 and fshift in E0:
                print a, f.factor(), fshift.factor()


def orig_shift(f, a):
    '''Return original shift of polynomial f by a.'''
    return (f(x+a)-f(a)).expand()

def orbit(f, q, nonzero=False):
    '''generator for orbit of f under original shifting over Fq.'''
    if nonzero:
        return [orig_shift(f, a) for a in GF(q, 'y') if a != 0]
    return [orig_shift(f, a) for a in GF(q, 'y')]

# d, e = 5, 2
# q = 3
# E = E(d, e, q)
#
# for f in E:
#     for g in orbit(f, q, nonzero=True):
#         if g in E:
#             print f, g
#

def cE(d,e):
    '''return count of exponential polynomials E_d,e.'''
    assert gcd(d, e) == 1
    if e == 1:
        return q^(d-1)
    else:
        return q^(floor(d/e))


# 2. gcd-free L
# =============

def gcd_free(L):
    assert gcd(L) == 1
    assert not ((1 in L) or (lcm(L) in L))
    if len(L) <= 2:
        return L
    i = 0    # pointer of opperation
    L.sort()
    while i < len(L)-1:
        G = [gcd(L[i], l) for l in L]
        G.sort()
        for j in range(G.count(1)):
            G.remove(1)    # ignore gcd = 1
        d = G[0]
        L = [l / gcd(d,l) for l in L]
        L[i] = d
        M = L[i+1:]    # remove duplicates in the unprocessed part
        M = list(set(M))
        L = L[:i+1] + M
        i += 1
    return L

def refineMat(dd, ee, verbose=False):
    '''refine ordered factorization dd and ee'''
    l = len(dd)
    m = len(ee)
    assert prod(dd) == prod(ee)
    CC0 =  [[1]*m + [dd[i]] for i in range(l)] + [ee + [1]]
    Clist = [matrix(CC0)]
    for i in range(0,l):
        for j in range(0,m):
            CCk = copy(Clist[-1])
            c = gcd(CCk[i,m], CCk[l,j])
            CCk[i,j] = c
            CCk[i,m] = CCk[i,m]/c
            CCk[l,j] = CCk[l,j]/c
            Clist.append(CCk)
    if verbose:
        return Clist

def refine(dd, ee, corefine=False):
    '''refine ordered factorization dd by ee.

    sage: refine([6,10],[10,6])
    [2, 3, 5, 2]
    sage: refine([6,35],[7,30])
    [6, 7, 5]
    sage: refine([6,7,5],[7,6,5])
    [6, 7, 5]
    '''
    m = len(dd)
    k = len(ee)
    assert prod(dd) == prod(ee)
    dd_new = [[1]*k + [d] for d in dd]
    ee_new = [[1]*m + [e] for e in ee]
    for i in range(k):
        for j in range(m):
            c = gcd(ee_new[i][-1], dd_new[j][-1])
            dd_new[j][i] = c
            ee_new[i][j] = c
            dd_new[j][-1] = dd_new[j][-1]/c
            ee_new[i][-1] = ee_new[i][-1]/c
    dd_new = [d for d in flatten(dd_new) if d != 1]
    ee_new = [e for e in flatten(ee_new) if e != 1]
    if corefine:
        return dd_new, ee_new
    return dd_new

def is_ref_ass(dd, ee, ff):
    '''check whether refine is associative

    sage: is_ref_ass([6,10], [10,6], [3,20])
    '''
    left = refine(dd, ee)
    LHS = refine(left, ff)
    print LHS
    right = refine(ee, ff)
    RHS = refine(dd, right)
    print RHS
    return LHS == RHS

def association(dd, ee):
    '''try and construct sigma(dd, ee)

    sage: association([2,2,2], [2,2,2])
    [0, 1, 2]
    '''
    assert prod(dd) == prod(ee)
    m = len(dd)
    k = len(ee)
    if m != k:
        return False
    ff = ee[:]
    sigma = []
    for d in dd:
        if d not in ee:
            return False
        j = ff.index(d)
        sigma.append(j)
        ff[j] = None
    return sigma

def are_associated(dd, ee):
    '''check whether two ordered factorizations are associated.'''
    assert prod(dd) == prod(ee)
    return refine(dd, ee) == dd and refine(ee, dd) == ee

def are_associated2(dd, ee):
    if association(dd, ee):
        return True
    return False

def refined_closure(DD):
    '''refine list of ordered factorizations.

sage: refined_closure([[6,10],[10,6]])
[[2, 3, 5, 2], [2, 5, 3, 2]]

sage: refined_closure([[2,15],[3,10],[5,6]])
[[2, 3, 5], [3, 5, 2], [5, 3, 2]]

sage: refined_closure([[12,420],[14,360],[20,252]])
'''
    if len(DD) == 1:
        return DD
    if len(DD) == 2:
        return list(refine(DD[0], DD[1], corefine=True))
    DD_old = refined_closure(DD[:-1])
    ee = DD[-1]
    DD_new = list(refine(dd,ee) for dd in DD_old) + [refine(ee,DD_old[0])]
    k = len(DD_new)
    return DD_new

def graph_from_relations(DD):
    '''return digraph G on dd = d0, d1, ..., d(m-1) and list of values for d.

    sage: G, dd0 = graph_from_relations([[2, 3, 5], [3, 5, 2], [5, 3, 2]])
    sage: G.show()

    '''
    DD = refined_closure(DD)
    dd0 = DD[0]
    m = len(dd0)
    g0 = {j: srange(j) for j in srange(m)}    # init with relations from sigma_0 (dd0, dd0) = id(m)
    for dd in DD:
        sigma = association(dd0, dd)
        g = {sigma.index(j): [sigma.index(i) for i in srange(j)] for j in srange(m)}
        g0 = {j: list(set(g0[j]) | set(g[j])) for j in g0}
    G = DiGraph(g0, multiedges=True, implementation='c_graph', vertex_labels=True)
    return G, dd0



def dag(G):
    '''return underlying DAG for given strongly connected G.

    sage: G = DiGraph({0: [1,2], 1: [0,2], 2: [0,1]}, multiedges=True)
    sage: DAG = dag(G)
    sage: DAG.show()


    '''
    assert G.is_strongly_connected()
    DAG = DiGraph({j: [i for i in G[j] if not j in G[i]] for j in G})
    assert DAG.is_directed_acyclic()
    return DAG

def commuting_neighborhood(G, v):
    '''return all vertices connected to v with 2-cycles.'''
    return [u for u in G.neighbors_out(v) if u in G.neighbors_in(v)]

def count_connected(G, dd0):
    '''return \# D_G with vertex labels given by dd0[vertex].

    Shifting has no effect iff single vertex.

    sage: G = DiGraph({0: [1, 2], 1: [0, 2], 2: [0, 1]}, multiedges=True)
    sage: dd0 = [2, 3, 5]
    sage: count_connected(G, dd0)
    (q - 1)*q

    sage: G = DiGraph({0: []})
    sage: dd0 = [5]
    sage: count_connected(G, dd0)
    q^4

    sage: G = DiGraph({0: [1], 1: [0]})
    sage: dd0 = [2, 3]
    sage: count_connected(G, dd0)
    q^4
    '''
    assert G.is_strongly_connected()
    count = 1
    disjoint_trig = False
    if len(G) == 1:
        v = G.vertices()[0]
        d = dd0[v]
        return q^(d-1)
    DAG = dag(G)
    V = DAG.topological_sort()[::-1]
    for v in V:
        d = dd0[v]
        Ud = [dd0[u] for u in commuting_neighborhood(G, v)]
        e = prod(Ud)    # or lcm
        assert gcd(d, e) == 1
        count *= cE(d, e)
        if d != 2 and e!= 2:
            disjoint_trig = True
    if disjoint_trig:
        count += q-1    # trigonometric
    count *= q      # original shifting
    return count




# 3. generating functions P, R, I, S, Q, E, A and their coefficients
# ==================================================================

def P(n):
    return q^(n-1)

def D(n, e):
    if e == 1 or e == n:
        return P(n)
    if e.divides(n):
        return q^(e+n/e-2)
    return 0

def Ritt2(n,l,m):
    assert l>1 and m>1
    assert l.divides(n) and m.divides(n)
    if l > m:
        l,m = m,l
    L = gcd(l,m)
    M = gcd(n/l, n/m)
    if L*M == 1:
        s = floor(m/l)
        return q^(2*L) * (q^(s-1) + int(l>2)*(1-q^(-1)))    # Corollary 6.3 from Ritt2
    return P(L)*C(n/(L*M),l/L,m/L)*P(M)

def Cold(n, L):
    'degree n, list L of components of left degrees'
    # remove duplicate entries
    L = list(set(L))
    # remove 1 and n from L
    if 1 in L:
        L.remove(1)
    if n in L:
        L.remove(n)
    # solve base cases
    if len(L) == 0:
        return P(n)
    if len(L) == 1:
        return D(n,L[0])
    # sanity check -- maybe superfluous
    for l in L:
        if not l.divides(n):
            return 0
    # define right list
    M = [n/l for l in L]
    # achieve coprimeness left and right
    lgcd = gcd(L)
    rgcd = gcd(M)
    if not (lgcd == 1 and rgcd == 1):
        return P(lgcd)*C(n/(lgcd*rgcd),[l/lgcd for l in L])*P(rgcd)
    # proceed for lgcd == rgcd == 1
    llcm = lcm(L)
    rlcm = lcm(M)
    # assert what we have not proven yet
    assert llcm == n and rlcm == n
    # case Ritt 3
    if len(L)>2:
        Lnew = gcd_free(L)
        Lnew.sort()
        m = Lnew[-1]
        l = n/m
        if l > m:
            return q^2
        return C(n,[l,m])
    # case Ritt 2; Cor 6.3 from Ritt2
    l = min(L[0],L[1])
    m = max(L[0],L[1])
    s = floor(m/l)
    return q^(2*lgcd) * (q^(s-1) + int(l>2)*(1-q^(-1)))

def Cnew(n, L):
    '''return collisions with left components L

    sage: Cnew(6, [2,3])

    '''
    assert 1 not in L and n not in L
    if len(L) == 0:
        return P(n)
    if len(L) == 1:
        return D(n, L[0])
    DD = [[l, n/l] for l in L]
    DD = refined_closure(DD)
    G, dd0 = graph_from_relations(DD)
    components = G.strongly_connected_components_subgraphs()
    count = 1
    for H in components:
        count *= count_connected(H, dd0)
    return count

def Dnq(n=30):
    '''return \#D_n(\Fq) as a polynomial in q.

    We have validated data for doctest:

    sage: Dnq(3)    # 0 for all primes
    0
    sage: Dnq(4)    # q^(2d-2) for square of a prime d
    q^2
    sage: Dnq(6)    # from Ritt2 for product of two distinct primes d*e
    2*q^3 - q^2      # CHECK THAT
    sage: Dnq(15)
    2*q^6 - 2*q^2 + q

    sage: Dnq(30)
    2*q^15 + 2*q^11 + 2*q^9 - q^8 - 6*q^7 - q^4 + q^2 + 2*q
    sage: Dnq(8)
    2*q^4 - q^3    # !!!CONSISTENT WITH EXPERIMENTS FOR q=3,5,7!!! :-)
    sage: Dnq(12)
    2*q^6 + 2*q^5 - 3*q^4 - q^2 + q
    sage: f.subs(q=5)
    35605
    sage: f.subs(q=7)
    261667
    '''
    assert n>1
    count = 0*q
    N = set(n.divisors())
    N.remove(1)
    N.remove(n)
    for L in subsets(N):
        if len(L) > 0:
            count += (-1)^(len(L)+1) * Cnew(n, list(L))
    return count.expand()

def bounds(n=30):
    '''check: bound seems to be wrong for n = 4 with q^2.

    Theorem 5.2? in Gathen2009p.'''
    assert n>1
    E = n.divisors()
    l = E[1]
    if n in [l, l^2]:
        l2 = 1
    else:
        l2 = E[2]
    s = floor(n/l^2)
    if n == l:
        alpha = 0
    elif n == l^2:
        alpha = q^(2*l-2)
    else:
        alpha = 2*q^(n/l+l-2)
    c = (n-l*l2)*(l2-l)/(l*l2)
    if n in [l, l^2, l^3, l*l2]:
        beta = 0
    else:
        beta = q^(-c)/(1-q^(-1))
    beta_star = q^(-n/l-l+s+3)
    if n in [l,l^2]:
        t = 0
    else:
        t = Cnew(n,[l,ZZ(n/l)])
    if n == l:
        return 0
    if n == l^2:
        return alpha.expand()
    if n == l^3:
        return (alpha*(1-q^(-(l-1)^2)/2)).expand()
    upper = alpha*(1-t/alpha+beta)    # 3.2 (i)
    if (l^2).divides(n):
        lower = alpha*(1-q^(-n/l+l+s-1)/2)
    else:
        lower = alpha*(1-beta_star)    # 3.2 (iii) for l^2 \nmid n
    return lower.expand(), upper.expand()


# 6. tables of explicit q-series
# ==============================

def D_table(N, threeplusdivs=False, withbounds=True):
    '''
    print LaTeX-table with exact formulae for #D_n(Fq) for composite n up to and including N.

    Previous results included exact formulae for n with 1 or 2 proper divisors and lower and upper bounds otherwise.

    Options
    - withbounds :: add column with previously known upper and lower bounds; (and empty entry if exact formulae was known -- and is already reproduced in the first column)
    - threeplusdivs :: only consider n with at least 3 proper divisors

    '''
    # start of the table
    t  = [r"\begin{tabular}{>{\centering\arraybackslash}p{0.05\textwidth}p{0.55\textwidth} "]
    if withbounds:
        t.append(r"p{0.4\textwidth} ")
    t.append(r"} \toprule")
    # first row
    t.append(r"$n$ & $\# D_{n} (\FF_{q})$")
    if withbounds:
        t.append(r" & lower bound, upper bound")
    t.append(r" \\ \midrule")
    # further rows
    ignore = prime_range(N+1)
    exactlyknown = [p*q for p in prime_range(ceil(N^1/2)) for q in prime_range(ceil(N^1/2))]
    exactlyknown += [p^3 for p in prime_range(ceil(N^1/3))]
    if threeplusdivs:
        ignore += exactlyknown
    for n in [n for n in srange(2,N+1) if n not in ignore]:
        t.append(r"{0} & ${1}$".format(n, latex(Dnq(n))))
        if withbounds:
            if n not in exactlyknown:
                t.append(r"& ${0}$".format(latex(bounds(n))[6:-7]))
            else:
                t.append(r" &")
        t.append(r" \\")
    t.append(r"\bottomrule")
    # add the last line and return
    t.append(r"\end{tabular}")
    return ''.join(t)

def Dickson_table(N):
    # start of the table
    t  = [r"\begin{tabular}{>{\centering\arraybackslash}p{0.05\textwidth}p{0.4\textwidth}p{0.4\textwidth}}"]
    t.append(r"\toprule")
    # first row
    t.append(r" $n$  & $D_{n}^{*}(x,z)$ & $D_{n}(x,z)$ \\")
    t.append(r"\midrule")
    # further rows
    for n in srange(0,N+1):
        t.append(r"{0} & ${1}$ & ${2}$ \\".format(n, latex(dickson_T(n,False)), latex(dickson_T(n,True))))
    t.append(r"\bottomrule")
    # add the last line and return
    t.append(r"\end{tabular}")
    return ''.join(t)



# 4. approximation functions \rho, \eta, \eps
# ===========================================

def rho(r,n,q):
    S = P(r,1,q)*P(r,n-1,q)/(1-q^(-b(r-1,n-1)))
    return S.simplify_full()

def eta(r,n,s,q):
    S = P(r,1,q)*P(r,n-s,q)
    return S.simplify_full()

def eps(r,n,q):
    ell = n.divisors()[1]
    S = P(r,n/ell,q^ell)/(ell*(1-q^(-ell*b(r-1,n/ell))))
    return S.simplify_full()

# 5. plotting the relative error
# ==============================

def RR_vs_rho_plot(r,n_list):
    '''
    graph containing relative errors (R_{r,n}(q)-rho_{r,n}(q))/rho_{r,n}(q) and the upper bound of
    '''
    upper_bound = 1/((1-q^(-1))*(1-q^(-r)))
    G = plot(upper_bound, 2, 20, color='black')
    G += text("$1/((1-\mathbf{q}^{-r})(1-\mathbf{q}^{-1}))$", (10, 1.5), color='black', fontsize=12)
    print 'calling generating function up to N =', max(n_list)
    S = RR(r,z,max(n_list))
    for n in n_list:
        print 'generating graph for n =', n
        numerator = expand(S.coeff(z^n) - rho(r,n,q))
        denominator = expand( rho(r,n,q) * q^(-binomial(n+r-2,r-1)+r*(r+1)/2))
        quotient = (numerator/denominator).simplify_full()
        X = srange(2,20,0.1)
        Y = [quotient(x).n() for x in X]
        G += list_plot(zip(X,Y), plotjoined=1, color='black')
        G += text("$n=%s$"%str(n), (1, quotient(2)), fontsize=12, color='black')
    return G

def QQ_vs_eta_plot(r,n_list,s):
    '''
    graph containing relative errors (Q_{r,n,s}(q)-eta_{r,n,s}(q))/eta_{r,n,s}(q) and the upper bound of
    '''
    G = plot([])
    print 'calling generating function up to N =', max(n_list)
    S = QQ(r,s,z,max(n_list))
    for n in n_list:
        print 'generating graph for n =', n
        numerator = expand(S.coeff(z^n) - eta(r,n,s,q))
        denominator = expand( eta(r,n,s,q) * q^(-binomial(n-s+r,r)+binomial(n-2*s+r,r)+r*(r+1)/2))
        quotient = (numerator/denominator).simplify_full()
        X = srange(2,20,0.1)
        Y = [quotient(x).n() for x in X]
        G += list_plot(zip(X,Y), plotjoined=1, color='black')
        G += text("$n=%s$"%str(n), (1, quotient(2)), fontsize=12, color='black')
    return G

def EE_vs_eps_plot(r,n_list):
    '''
    graph containing relative errors (E_{r,n}(q)-eps_{r,n}(q))/eta_{r,n}(q) and the upper bound of
    '''
    G = plot([])
    print 'calling generating function up to N =', max(n_list)
    S = EE(r,z,max(n_list))
    for n in n_list:
        print 'generating graph for n =', n
        ell = n.divisors()[1]
        numerator = expand(S.coeff(z^n) - eps(r,n,q))
        denominator = expand( eps(r,n,q) * q^(-(ell-1)*(b(r-1,n/ell)-r)-1))
        quotient = (numerator/denominator).simplify_full()
        X = srange(2,10,0.1)
        Y = [quotient(x).n() for x in X]
        G += list_plot(zip(X,Y), plotjoined=1, color='black')
        G += text("$n=%s$"%str(n), (1, quotient(2)), fontsize=12, color='black')
    return G

def refineMatStr(dd, ee, first, last):
    Clist = refineMat(dd, ee, verbose)
    l = len(dd)
    m = len(ee)
    t = []
    for k in range(first, last+1):
        t.append(r"C^{{({0})}} = ".format(k))
        t.append(r"\begin{pmatrix}")
        Mat = latex(Clist[k])
        first_break = Mat.find('\n')
        last_break = Mat.rfind('\n')
#        t.append(r"2 & 3")
        t.append(Mat[first_break:last_break+1])
        t.append(r" \end{pmatrix}")
        if k < last:
            t.append(r",\quad ")
#            if k%3 == 2:
#                t.append(r"\\ ")
#            t.append("\n")
    return ''.join(t)
    t = ''.join(t)
    # t = t.replace(r"\n", " ")    # sagetex can't handle newlines
    return t
