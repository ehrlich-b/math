# Euclidean Jordan algebras in Lean

This library formalizes power associativity, spectral decomposition, the
trace form, the cone of squares, unital order automorphisms, and the Peirce
decomposition relative to a Jordan frame. It includes a Hermitian matrix
model. Module docstrings name the mathematical sources and explain the
hypotheses used in Lean. The [source index](../../ATTRIBUTION.md) links to
the original publications.

From the library directory, run `lake build` followed by
`lake env lean AxiomAudit.lean`. The audit checks module coverage,
the axiom closure of declarations in the library, and the Hermitian model.

The [notice](NOTICE) records the Apache-2.0 terms and changes made for this
distribution. The bundled [physlib source record](EuclideanJordan/Vendor/VENDOR.md)
credits Alex Meiburg and Leonardo A Lessa.
