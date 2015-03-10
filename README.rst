*****************************************************
Decomposing Univariate Polynomials over Finite Fields
*****************************************************

This Python-module provides functions to study the functional
decomposition of univariate polynomials over a finite field. We have
the following fundamental distinctions.

Tame case
    where the polynomial's degree is coprime to the characteristic of
    the base field.

Wild case
    where the polynomial's degree is a multiple of the characteristic
    of the base field.

Additive case
    where all exponents of the polynomial are powers of the
    characteristic of the base field; this is a special case of the
    previous one.

We measure the degree of our understanding by our ability to count the
number of decomposable polynomials at a given degree. The crucial
ingredient for the obvious inclusion-exclusion formula is an
understanding of *collisions*, that is of distinct decompositions of a
given polynomial.

Submodules
==========

add_count.sage
    for a basic additive case, this gives the exact
    number of decomposable polynomials according to [GGZ10]_; also
    comparison with the numbers of [CHH04]_.

additive_collisions.sage
    for the (general) additive case, this determines the number and
    structure of all decompositions of an additive polynomial via the rational Jordan
    form of the Frobenius on its root space; see [GGZ10]_ and [F11]_.

compose_by_brute_force.sage
    create look-up tables of complete decompositions (if feasible) or
    count at least the number of decomposables; output to ./data/

p2_decompose.sage
    for the (basic) wild case, create dictionaries to classify
    decompositions; see [BGZ13]_.

p2_construct_collision_by_parameter.sage
    for the (basic) wild case, create polynomials with a given number
    of decompositions TODO

tame_collisions.sage
    for the tame case, determine the structure (and number) of all
    tame collisions according to [Z14]_.


Usage
=====

Load the module in your local Sage installation::

   $ sage -q
   sage: load('add_count.sage')

See each module's documentation for further instructions.


Output
======

Folder structure::

    ./data/
        - C_n_q.sobj
        - D_n_q.sobj
        - Dd_n_q.sobj
        - Dtext_n_q.txt
        - numbers.txt

For internal use::

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


Polynomials
===========

tame dictionaries
-----------------

legend: Y (counting available), YY (counting and dictionary
available), EOM (out of memory), EOT (out of time), NN (user abort), ? (untested)

====  === ===  ===  ===   ===
n\\q    2   3    4    5     7
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

Composite degrees with more than 2 prime factors (counted with
multiplicity) are marked with \*.


additive dictionaries
---------------------

suggestions:

r = 4 => q = 16, n = 256
         q = 64, n = 4,(16?)
r = 8 => q = 8, n = 8, 64
         q = 64, n = 8, 64

r = 3 => q = 3, n = 3, 9, 27, 81, 243, 729
         q = 9, n = 3, 9, 27, 81
	 q = 27, n = 3, 9, 27, 81
r = 9 => q = 9, n = 9, 81, 729
         q = 81, n = 9, 81

r = 5 => q = 5, n = 5, 25, 125, 625
	 q = 25, n = 5, 25, 125, 625?
r = 25 =>q = 25, n = 25, 625, (3125?!)
         q = 625, n = 25, 625

actual data:

==== === === === === === === === === === === ==== === === === === === ===
n\\q  2   3   4   5   7   8   9   11  13  16  25   27  32  64  81 125 625
==== === === === === === === === === === === ==== === === === === === ===
2    2       2           2               2            2   2
3        3                   3                    3
4    2       2,4         2               2,4          2   2
5                 5                          5
8    2       2           2               2            2   2
9        3                   3,9                  3            9
16   2       2,4         2               2,4
25                5                          5,25                     25
27       3                   3                    3
32   2       2           2
64   2       2,4                         4
81       3                   3,9                               9
125               5                          5
128  2       2
243      3
256  2       4                           4
512  2
625               5                          25                       EOM
729      3                   9
1024 2       4
2048 2
==== === === === === === === === === === === ==== === === === === === ===


Todos
=====

- add the formulas of [BGZ13]_ to ``p2_construct_collision_by_parameter.sage``


Requirements
============

This code requires the free mathematical software [Sage]_ which is
available for download at http://www.sagemath.org and as cloud service
at https://cloud.sagemath.org. It has been tested under GNU/Linux with
Sage 6.4.


References
==========

.. [BGZ13] Raoul Blankertz, Joachim von zur Gathen & Konstantin
	   Ziegler (2013). Compositions and collisions at degree
	   p\ :sup:`2`. *Journal of Symbolic Computation* **59**,
	   113–145. ISSN 0747-7171. URL
	   http://dx.doi.org/10.1016/j.jsc.2013.06.001. Also available
	   at http://arxiv.org/abs/1202.5810.  Extended abstract in
	   *Proceedings of the 2012 International Symposium on Symbolic
	   and Algebraic Computation ISSAC ’12*, Grenoble, France
	   (2012), 91–98.

.. [CHH04] Robert S. Coulter, George Havas & Marie Henderson
	   (2004). On decomposition of sub-linearised
	   polynomials. *Journal of the Australian Mathematical
	   Society* **76**\(3), 317–328. URL
	   http://dx.doi.org/10.1017/S1446788700009885.

.. [F11] Harald Fripertinger (2011). The number of invariant subspaces
	 under a linear operator on finite vector spaces. *Advances in
	 Mathematics of Communications* **5**\(2), 407–416. ISSN
	 1930-5346. URL http://dx.doi.org/10.3934/amc.2011.5.407.

.. [GGZ10] Joachim von zur Gathen, Mark Giesbrecht & Konstantin
	   Ziegler (2010). Composition collisions and projective
	   polynomials. Statement of results. In *Proceedings of the
	   2010 International Symposium on Symbolic and Algebraic
	   Computation ISSAC ’10*, Munich, Germany, edited by Stephen
	   Watt, 123–130. ACM Press. URL
	   http://dx.doi.org/10.1145/1837934.1837962. Preprint
	   available at http://arxiv.org/abs/1005.1087.

.. [Sage] W. A. Stein et al. (2014). Sage Mathematics Software
  (Version 6.4). The Sage Development Team. URL
  http://www.sagemath.org.


.. [Z14] Konstantin Ziegler (2014). Tame decompositions and
	 collisions. In *Proceedings of the 2014 International
	 Symposium on Symbolic and Algebraic Computation ISSAC ’14*,
	 Kobe, Japan, edited by Katsusuke Nabeshima, 421–428. ACM
	 Press, Kobe, Japan. URL
	 http://dx.doi.org/10.1145/2608628.2608653. Preprint available
	 at http://arxiv.org/abs/1402.5945.


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
along with this program.  If not, see http://www.gnu.org/licenses/.
