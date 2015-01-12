************************
Decomposable Polynomials
************************

This Sage-module provides functions to study the decomposition of
univariate polynomials over finite field. We measure the degree of our
understanding by our ability to count the decomposables approximately
and exactly. The crucial ingredient for any inclusion-exclusion formula to do so
requires an understanding of collisions, that is of distinct decompositions of a
given polynomial.

Submodules
==========

tame_collisions.sage
    determine the structure (and number) all tame collisions for a given a set of ordered factorizations

compose_by_brute_force.sage
    create look-up tables of complete factorizations; output to ./data/

add_count.sage
    implementation of the (wild) counting formulas of GGZ, also comparison with
    CoulterHavasHenderson2004

additive_collisions.sage
    determine all decompositions of additive polynomials via the rational Jordan
    form of the Frobenius on its root space

p2_decompose.sage
p2_construct_collision_by_parameter.sage
    TODO BGZ


Output
======

./TO_SORT--old
    fifi*
    /data/
        - C
        - D
        - I
        - P
        - email n=25, q=5
        - old for comparison incl. n=18, q=9 and more wild stuff
     /report/

./data/
    - C_n_q.sobj
    - D_n_q.sobj
    - Dd_n_q.sobj
    - Dtext_n_q.txt
    - numbers.txt


Polynomials
===========

dictionaries and sets of monic original polynomials at degree n over Fq

Q: store complete or incomplete decompositions
A: we opt for complete, since this is the more refined picture

Note: this requires testing for indecomposability of every component (maybe
expensive); if that is too costly, simply loop over all polynomials, obtain
all decompositions and write a post-processing procedure to "filter" the
underlying indecomposable ones

Experience: storing P_n_q or I_n_q is infeasible even for small values (like
n=30, q=2).
Consequence: store only D_n_q and C_n_q; produce I_n_q dynamically

see ``compose_by_brute_force.sage`` for detailed specification

- dict Dd_n_q    # if this computation runs out of memory -- maybe at least
  counting is possible
- set D_n_q vs. Dtext_n_q
- set C_n_q

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
 18*   Y   Y    Y   YY     ?
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
====  === ===  ===  ===   ===
1155
2310
====  === ===  ===  ===   ===

additive dictionaries

r = 4 => q = 16, n = 256
         q = 64, n = 4,(16?)
r = 8 => q = 8, n = 8, 64
         q = 64, n = 8, 64

r = 3 => q = 3, n = 3, 9, 27, 81, 243, 729
         q = 9, n = 3, 9, 27, 81
	 q = 27, n = 3, 9, 27, 81
r = 9 => q = 9, n = 9, 81, 729
         q = 81, n = 9, 81
r = 27

r = 5 => q = 5, n = 5, 25, 125, 625
	 q = 25, n = 5, 25, 125, 625?
r = 25 =>q = 25, n = 25, 625, (3125?!)
         q = 625, n = 25, 625

r = 7

==== === === === === === === === === === === === === === === === === ===
n\q   2   3   4   5   7   8   9   11  13  16  25  27  32  64  81 125 625
==== === === === === === === === === === === === === === === === === ===
2    2       2           2               2           2   2
3        3                   3                   3
4    2       2,4         2               2,4         2   2
5                 5                          5
8    2       2           2               2           2   2
9        3                   3,9                 3            9
16   2       2,4         2               2,4
25                5                          5,25                    25
27       3                   3                   3
32   2       2           2
64   2       2,4                         4
81       3                   3,9                              9
125               5                          5
128  2       2
243      3
256  2       4                           4
512  2
625               5                          25                      EOM
729      3                   9
1024 2       4
2048 2
==== === === === === === === === === === === === === === === === === ===

References
==========

- Reinhold Burger and Albert Heinle, Diffie Hellman -- Non commutative version
  http://github.com/ioah86/diffieHellmanNonCommutative.

- Xavier Caruso, skew_polynomial

- Manuel Kauers and Maximilian Jaroschek and Fredrik Johansson, Ore Polynomials in
  Sage, http://arxiv.org/abs/1306.4263v1.

- W. A. Stein et al. (2014). Sage Mathematics Software (Version
  6.3). The Sage Development Team. URL http://www.sagemath.org.


Author
======

- Konstantin Ziegler (2013-12-24): initial version

License
=======

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
