# Attribution

## Mathematical sources

The [Euclidean Jordan library](vendor/euclidean-jordan/) uses the following
sources. The module docstrings give local theorem or section references.

| Human authors | Source | Role |
| --- | --- | --- |
| Abraham Adrian Albert | *Power-associative rings* (1948). [DOI](https://doi.org/10.1090/S0002-9947-1948-0027750-7) | Power associativity and the singly generated subalgebra |
| Jacques Faraut and Adam Korányi | *Analysis on Symmetric Cones* (1994). [Oxford University Press](https://academic.oup.com/book/54470) | Jordan algebra structure, spectral theory, order and Peirce theory |
| Erik M. Alfsen and Frederic W. Shultz | *Geometry of State Spaces of Operator Algebras* (2003). [Springer](https://doi.org/10.1007/978-1-4612-0019-2) | Order-unit spaces and Theorem 2.80 on Jordan automorphisms |
| Max Koecher | *The Minnesota Notes on Jordan Algebras and Their Applications* (1999). Edited by Aloys Krieg and Sebastian Walcher. [Springer](https://doi.org/10.1007/BFb0096285) | Historical background on the relation between cones and Jordan algebras |
| Kevin McCrimmon | *A Taste of Jordan Algebras* (2004). [Springer](https://doi.org/10.1007/b97489) | §II.8, Peirce theory without Euclidean hypotheses |
| Nathan Jacobson | *Structure and Representations of Jordan Algebras* (1968). [AMS](https://doi.org/10.1090/coll/039) | Coordinatization background for the identities in `Connection.lean` |
| John van de Wetering | *Sequential Product Spaces are Jordan Algebras* (2019). [Journal DOI](https://doi.org/10.1063/1.5093504), [arXiv:1803.11139](https://arxiv.org/abs/1803.11139) | Order-unit notation and Proposition 5.3 |
| Hendrik van Imhoff and Mark Roelands | *Order isomorphisms between cones of JB-algebras* (2019). [arXiv:1904.09278](https://arxiv.org/abs/1904.09278) | Related results for JB-algebras, §§2.3 and 4.3 |

## Supporting code

- Alex Meiburg and Leonardo A Lessa wrote the included physlib modules
  (2025–2026). Lessa co-authored `HermitianMat/Proj.lean`. The remaining
  included modules credit Meiburg. The [file inventory and edit record](vendor/euclidean-jordan/EuclideanJordan/Vendor/VENDOR.md)
  maps each module to its upstream location. [Pinned physlib tree](https://github.com/leanprover-community/physlib/tree/a50684a1919e84dc1c761028ff4f77cd59e2de6b)
- The Lean and Mathlib communities supply the proof assistant and its
  mathematical library. The [toolchain](lean-toolchain) and
  [manifest](lake-manifest.json) give the version and dependency pins.

## Notebook and manuscripts

- The bbchallenge community publishes the recurrence studied in the notebook's
  threshold-trap result. Its machine was discovered by mxdys in 2024.
  [Beaver Math Olympiad, Problem 5](https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad#5._1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE_(bbch))
- See the [manuscript citations](original/papers/README.md) for Bryan Ehrlich's
  Papers A and B.
