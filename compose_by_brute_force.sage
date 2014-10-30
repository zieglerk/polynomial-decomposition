'''
Given n and q compute all complete (!) (de)compositions of polynomials at degree n over Fq

Input:
-

Output:
- Dd_n_q :: dict with decomposable f as keys and lists of complete decompositions as values [[g1,g2], [h1,h2,h3], ...]; purpose: decompose by table-lookup
- D_n_q :: set of all decomposable f; purpose: recursion
- C_n_q :: set of all 2-collisions to compare with explicit constructions like Ritt2 and Frob; purpose: check counting

Always: monic original
Legacy note: n used to be r^2 with default r = char(q)

Usage:

    $ sage compose_by_brute_force.sage [degree n=6] [field size q=2] [with_decomp=true]
'''

import sys, subprocess, itertools

def ord_facts(n):
    '''Return a list of ordered factorizations of the integer ``n``.

    sage: ord_facts(9)
    [[3, 3], [9]]
    sage: ord_facts(27)
    [[3, 3, 3], [3, 9], [9, 3], [27]]
    '''
    if n == 1:
        return []
    elif n.is_prime():
        return [ [n] ]    # = [ n.divisors()[1:] ]
    return [ [l0] + L1 for l0 in n.divisors()[1:] for L1 in ord_facts(n.divide_knowing_divisible_by(l0)) ] + [ [n] ]

def num_comp(n, q):
    '''return an upper bound for the number of decompositions based on #I ~ #P.'''
    return sum([q^(d+n.divide_knowing_divisible_by(d)-2) for d in n.divisors()[1:-1]])

def compose(decomposition):
    '''given a list of polynomials return their composition

    sage: R.<x> = PolynomialRing(GF(7), 'x')
    sage: decomposition = [R.random_element() for _ in range(3)]
    sage: decomposition
    [5*x^2 + 5*x + 5, 6*x^2 + 6*x + 3, 2*x^2 + 5*x + 4]
    sage: compose(decomposition)
    3*x^8 + 2*x^7 + 3*x^6 + 5*x^5 + 5*x^4 + 5*x^3 + 5*x

    sage: compose([x^2,x+1])
    x^2 + 2*x + 1
    '''
    m = len(decomposition)
    f = decomposition[0]
    for i in range(1, m):
        f = f.subs(x = decomposition[i])
    return f

def I(s, q):
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
    R.<x> = PolynomialRing(GF(q, 'y'), 'x')
    if len(s) == 1:
        if n.is_prime():
           return (f*x for f in R.monics(of_degree=n - 1))
        else:
            Dec = load('data/D_'+str(n)+'_'+str(q))
            return (f*x for f in R.monics(of_degree=n - 1) if R(f*x) not in Dec)
    Isequence = [I([d], q) for d in s]
    return itertools.product(*Isequence)

def D(n, q, with_decomp=true):
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
    cent = 1 + num_comp(n, q)//100    # round up
    comp_counter = 0
    num_sequences = len(ord_facts(n)) - 1    # ignore [n]
    sequence_counter = 0
    for sequence in ord_facts(n):
        if len(sequence) == 1:
            continue
        sequence_counter += 1
        print 'composing', sequence, 'as number', sequence_counter, 'of',  num_sequences, 'degree sequences'
        for decomposition in I(sequence, q):
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

args = sys.argv

# defaults
n = 6
q = 2
with_decomp = true

if len(args) > 1:
    n = ZZ(args[1])
if len(args) > 2:
    q = ZZ(args[2])
if len(args) > 3:
    with_decomp = false

print 'Running with parameters', n, q, with_decomp

D = D(n, q, with_decomp=with_decomp)
suffix = '_'+str(n)+'_'+str(q)
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
fileobject = open('data/numbers.txt', 'a')
fileobject.write(str(n).rjust(4)+' '+str(q).rjust(2)+' '+str(N)+'\n')
fileobject.close()
os.system("sort -u data/numbers.txt -o data/numbers.txt")

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
