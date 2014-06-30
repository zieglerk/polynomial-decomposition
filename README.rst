decomposable polynomials (2013-12-24)
=====================================

This package contains code to count decomposable polynomials over finite fields.
The crucial intermediate step for any inclusion-exclusion formula to do so
requires an understanding of collisions, that is of distinct decompositions of a
given polynomial.

submodules
==========

Mark Giesbrecht's Maple code for add_coll
    counts Jordan rational forms (?)

Christian Gorzel's singular code
    implements Joachim's decomposition algorithm (?)

polynomials
===========

dictionaries and sets of monic original polynomials at degree n over Fq

Q: store complete or incomplete decompositions
A: we opt for complete, since this is the more refined picture

Note: this requires testing for indecomposability of every component (maybe
expensive);  if that is too costly, simply loop over all polynomials, obtain
all decompositions and write a post-processing procedure to "filter" the
underlying indecomposable ones

Experience: storing P_n_q or I_n_q is infeasible even for small values (like
n=30, q=2).
Consequence: store only D_n_q and C_n_q; produce I_n_q dynamically

see ``compose_by_brute_force.sage`` for detailed specification

- dict D_n_q    # if this computation runs out of memory -- maybe at least
  counting is possible
- dict P_n_q
- Set I_n_q
- Set C_n_q

prime powers q (up to 30)
composite n (as large as possible)
- level 1: n is prime DONE
- level 2: n is product of two primes (maybe identical): 33, 35, 39, 49, 55, 65, 77, 91


mark* all composites with more than 2 prime factors (counted with multiplicity)

====  === ===  ===  ===   ===
n\q    2   3    4    5     7
====  === ===  ===  ===   ===
   4   Y   Y    Y    Y     Y
   6   Y   Y    Y    Y     Y
  8*   Y  YY    Y   YY    YY
   9   Y   Y    Y    Y     Y
  10   Y   Y    Y    Y     Y
 12*   Y   Y    Y   YY    YY   
  14   Y   Y    Y    Y     Y 
  15   Y   Y    Y    Y     Y
 16*   Y  YY    Y   YY     ?
 18*   Y   Y        YY     ?
 20*   Y  YY              EOM
  21   Y   Y
  22   Y   Y
 24*   Y            EOT   EOT
  25   Y
  26   Y
 27*  YY        NN   ?     ?
 28*   Y   NN        ?
 30*   Y                  EOT
 32*      EOT        -     -
  35   Y   ?    ?
 36*                 ?	   ?
 42*                EOT
 64*       ?         ?     ?
 81*  EOT       -    -     -
105*  EOT       -
125    ?   ?    ?          ?

1155
2310

