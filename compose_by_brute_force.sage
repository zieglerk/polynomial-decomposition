'''
Compute all decomposable polynomials at degree n over Fq. We restrict ourselves to monic original polynomials.

If size permits, we also store all complete (!) decompositions of a decomposable polynomial for instant decompositions later.

Optionally, compute all decomposable r-additive polynomials of degree n (=r^m for exponent m). Design decision: work with degree (instead of the more natural exponent to keep the interface unified)

Input:
- n :: composite integer (degree of polynomials under consideration)
- q :: prime power (size of coefficient field)
- with_decomp :: Boolean (decompositions in a dictionary)
- r :: prime power (optional, additivity of polynomials)

Output:
- Dd_n_q/Dd_n_q_r-add-sqf :: dict with (additive) decomposable f as keys and lists of complete decompositions as values [[g1,g2], [h1,h2,h3], ...]; purpose: decompose by table-lookup
- D_n_q/D_n_q_r-add-sqf :: set of all decomposable f; purpose: recursion
- C_n_q/C_n_q_r-add-sqf :: set of all 2-collisions to compare with explicit constructions like Ritt2 and Frob; purpose: check counting

Usage:

    $ sage compose_by_brute_force.sage [degree n=6] [field size q=2] [with_decomp=true] [additivity r=1]

Our experiments use |assert q.is_power_of(r)|, but the general situation does not require that.

'''

import sys, subprocess, itertools

args = sys.argv

# defaults
n = 6
q = 2
with_decomp = true
r = 1
only_additive = false

if len(args) > 1:
    n = ZZ(args[1])
if len(args) > 2:
    q = ZZ(args[2])
if len(args) > 3:
    with_decomp = bool(args[3])
if len(args) > 4:
    r = ZZ(args[4])
    if r > 1:
        only_additive = true
        assert n.is_power_of(r)
        m = n.log(r)

print 'Running with parameters n =', n, ', q =', q, ', with_decomp =', with_decomp, ', r =', r

def ord_facts(n, r=1):
    '''Return a list of all ordered factorizations of the integer ``n``.

    In the additive case, n must be a power of r and only factorizations of n into powers of r are allowed.

    sage: ord_facts(9)
    [[3, 3], [9]]
    sage: ord_facts(27)
    [[3, 3, 3], [3, 9], [9, 3], [27]]
    sage: ord_facts(16, r=4)
    [[4, 4], [16]]
    sage: ord_facts(16, r=2)
    [[2, 2, 2, 2], [2, 2, 4], [2, 4, 2], [2, 8], [4, 2, 2], [4, 4], [8, 2], [16]]
    '''
    if n == 1:
        return []
    elif n.is_prime():
        return [ [n] ]    # = [ n.divisors()[1:] ]
    elif r > 1:
        assert n.is_power_of(r)
        m = n.log(r)
        return [ [r^i] + remainder for i in srange(1,m) for remainder in ord_facts(r^(m-i), r) ] + [ [n] ]
    return [ [l0] + L1 for l0 in n.divisors()[1:] for L1 in ord_facts(n.divide_knowing_divisible_by(l0)) ] + [ [n] ]

def num_bicomp(n, q):
    r"""
    Return the number of all (bi-)compositions that yield a decomposable polynomials of degree n. This serves as an upper bound for the number of compositions (of indecomposable polynomials) that will be executed. (Upper bound, because a degree-m1-m2-m3 tri-composition is counted twice. On the other hand, each of the three components m1-m2-m3 is chosen indecomposably -- which lowers the total number again. TODO) OK, let's just call it an estimate. After all, that's what it's used for.

    TODO: check that/whether this also applies in the wild case.

    TODO: adapt additive upper bound in the same spirit.
    """
    return sum([q^(d+n.divide_knowing_divisible_by(d)-2) for d in n.divisors()[1:-1]])

def compose(polynomials):
    '''given a list of polynomials return their composition

    sage: R.<x> = PolynomialRing(GF(7), 'x')
    sage: polynomials = [R.random_element() for _ in range(3)]
    sage: polynomials
    [5*x^2 + 5*x + 5, 6*x^2 + 6*x + 3, 2*x^2 + 5*x + 4]
    sage: compose(polynomials)
    3*x^8 + 2*x^7 + 3*x^6 + 5*x^5 + 5*x^4 + 5*x^3 + 5*x

    sage: compose([x^2, x + 1])
    x^2 + 2*x + 1
    '''
    m = len(polynomials)
    f = polynomials[0]
    for i in range(1, m):
        f = f.subs(x = polynomials[i])
    return f

def I(s, q, r=1):
    r"""
    Return an iterator over complete decompositions with degree sequence s.

    CAVE: the output format for single-element ``s`` is special (see below).

    INPUT:

    - ``s`` -- non-empty sequence of integers.
    - ``q`` -- field size.

    OUTPUT:

    - generator of indecomposable polynomials (if len(s) == 1) or generator of lists of indecomposable polynomials (otherwise).

    EXAMPLES::

        sage: G = I([2], 5)
        sage: for g in G:
        ....: print g
        ....:
        x^2
        x^2 + x
        x^2 + 2*x
        x^2 + 3*x
        x^2 + 4*x

        sage: G = I([2, 3], 2)
        sage: for g in G:
        ....: print g
        ....:
        (x^2, x^3)
        (x^2, x^3 + x)
        (x^2, x^3 + x^2)
        (x^2, x^3 + x^2 + x)
        (x^2 + x, x^3)
        (x^2 + x, x^3 + x)
        (x^2 + x, x^3 + x^2)
        (x^2 + x, x^3 + x^2 + x)

        sage: G = I([2,2,3], 5)
        sage: sum(1 for _ in G)
        625

    """
    assert len(s) > 0
    assert q.is_prime_power()
    n = prod(s)
    assert n > 1
    F = GF(q, 'y')
    R.<x> = PolynomialRing(F, 'x')
    if len(s) == 1:
        if r > 1:
            assert n.is_power_of(r)
            m = n.log(r)
            if m == 1:
                return (x^r + a*x for a in F if a <> 0)
            else:
                Dec = load('data/D_'+str(n)+'_'+str(q)+'_'+str(r)+'-add-sqf')
                All = [x^n + sum([avec[i-1]*x^(r^i) for i in range(1,m)]) + a*x for avec in itertools.product(F, repeat = m - 1) for a in F if a <> 0]
                return (f for f in All if f not in Dec)
        if n.is_prime():
           return (f*x for f in R.monics(of_degree=n - 1))
        else:
            Dec = load('data/D_'+str(n)+'_'+str(q))
            return (f*x for f in R.monics(of_degree=n - 1) if R(f*x) not in Dec)
    Isequence = [I([d], q, r) for d in s]
    return itertools.product(*Isequence)

def D(n, q, with_decomp=true, r=1):
    '''Given n and q return a dictionary of all monic, original
    decomposable polynomials over GF(q) at degree n as keys with a
    list of complete decompositions as values.
    '''
    # define the polynomial ring
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    # initialize D
    if with_decomp:
        D = {}
    else:
        target = 'data/Dtext_'+str(n)+'_'+str(q)+'.txt'
        D = open(target, 'a')
    # upper bound for number of compositions
    cent = 1 + num_bicomp(n, q)//100    # round up
    comp_counter = 0
    num_sequences = len(ord_facts(n, r)) - 1    # ignore [n]
    sequence_counter = 0
    for sequence in ord_facts(n, r):
        if len(sequence) == 1:
            continue
        sequence_counter += 1
        print 'composing', sequence, 'as number', sequence_counter, 'of',  num_sequences, 'degree sequences'
        for decomposition in I(sequence, q, r):
            f = compose(decomposition)
            comp_counter += 1
            if with_decomp:
                try:
                    D[f].append(decomposition)
                except KeyError:
                    D[f] = [decomposition]
            else:
                D.write(str(f)+'\n')
            if cent.divides(comp_counter):
                print comp_counter, 'compositions executed: ', comp_counter/cent, '%'
    if not with_decomp:
        D.close()
        print 'Done writing decomposables to file, now UNIX will sort.'
        os.system("sort -u "+target+" -o "+target)
        return
    return D

D = D(n, q, with_decomp=with_decomp, r=r)
suffix = '_'+str(n)+'_'+str(q)
if r > 1:
    suffix += '_'+str(r)+'-add-sqf'
print 'DONE with composition, now counting and storing the number.'
if with_decomp:
    N = len(D)
else:
    target = 'data/Dtext'+suffix+'.txt'
    p = subprocess.Popen(['wc', '-l', target], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    result, err = p.communicate()
    if p.returncode != 0:
        raise IOError(err)
    N = int(result.strip().split()[0])
# TODO not ready for use with additive numbers yet
# fileobject = open('data/numbers.txt', 'a')
# fileobject.write(str(n).rjust(4)+' '+str(q).rjust(2)+' '+str(N)+'\n')
# fileobject.close()
# os.system("sort -u data/numbers.txt -o data/numbers.txt")

print 'Done counting, now extracting collisions if required.'

if with_decomp:
    C = []
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    cent = 1 + len(D)//100    # round up
    comp_counter = 0
    print 'START filtering 2-collisions.'
    for f in D:
        comp_counter += 1
        k = len(D[f])
        if k > 1:
            C.append(f)
        if cent.divides(comp_counter):
            print comp_counter, 'polynomials checked: ', comp_counter/cent, '%'
    save(D, 'data/Dd'+suffix)
    print 'extract keys from Dd and save as dictionary with None values'
    save({f:None for f in D}, 'data/D'+suffix)
    print 'save C as dictionary with None values'
    save(dict.fromkeys(C), 'data/C'+suffix)
print 'DONE.'
