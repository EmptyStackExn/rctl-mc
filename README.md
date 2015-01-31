rctl-mc
===================

> An automata-theoretic model-checker for safety properties of pushdown systems with `RCTL` (also called `CTL + Rollback`) operators.


Building and running
-------------------

To build the sources you have fetched, you can simply type the following

	make

Finally, `rctl-mc` takes as input a file containing a pushdown system and a file with properties expressed in `RCTL`.


Scientific aim
-------------------
The aim of `RCTL` is to provide a branching-time logic with non-determined past modalities (called _rollback operators_). In particular, we focus on the model-checking problem on pushdown systems. Compared to traditional branching-time logics of the kind of `CTL`, it has been shown that past-time operators provide many interesting properties. In this way, it appears they

1. allow easier and more natural temporal specifications (Lichtenstein, 1985)
2. can be exponentially more succint than forward-only specifications (Laroussinie, 2002)
3. preserve `EXPTIME`-completeness property against full-modal μ-calculus (Vardi, 1998)


License
-------------------

This is not free software. This release can be used for evaluation, research and education purposes, but not for commercial purposes. The copyright to this code is held by [Université Paris-Sud](http://www.u-psud.fr) and distributed under the INRIA Non-Commercial License Agreement. All rights reserved.

THE PROVIDER MAKES NO REPRESENTATIONS ABOUT THE SUITABILITY, USE, OR PERFORMANCE OF THIS SOFTWARE OR ABOUT ANY CONTENT OR INFORMATION MADE ACCESSIBLE BY THE SOFTWARE, FOR ANY PURPOSE. THE SOFTWARE IS PROVIDED "AS IS," WITHOUT EXPRESS OR IMPLIED WARRANTIES INCLUDING, BUT NOT LIMITED TO, ANY IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, OR NONINFRINGEMENT WITH RESPECT TO THE SOFTWARE. THE PROVIDER IS NOT OBLIGATED TO SUPPORT OR ISSUE UPDATES TO THE SOFTWARE.


Hai Nguyen Van <nguyen-van@lri.fr>
