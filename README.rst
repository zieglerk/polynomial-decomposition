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
    for *all* additive polynomials this gives the exact number of
    $k$-collisions and by inclusion-exclusion the number of
    decomposables; see [GGZ10]_, compare to [CHH04]_.

add_decompose.sage
    for a *single* additive polynomial, this determines the structure
    of (the lattice of) right components via the rational Jordan
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


Todos
=====

- add the formulas of [BGZ13]_ to ``p2_construct_collision_by_parameter.sage``
- compare with the ore-package and sigma(a) = a^r

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
