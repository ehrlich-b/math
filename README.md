# Math in Lean

Lean formalizations curated by Bryan Ehrlich. The repository contains proofs
and statements from two manuscripts, a selection of exploratory notebook
results, and a library of classical Jordan algebra.

- [Original work](original/papers/) contains the Lean statements, bridges, and
  proofs for Papers A and B. [Musings](original/musings/) contains exploratory
  results from the notebook.
- [Formalized mathematics](formalized/proofs/) is where daily exports of
  proofs of published results will go. The
  [Euclidean Jordan library](vendor/euclidean-jordan/) formalizes classical
  results and has its own license notice. [Attribution](ATTRIBUTION.md)
  credits the mathematicians and upstream code.

AI models generated much of the proof code under Bryan Ehrlich's direction.
Lean checks the proofs against their formal statements. Declarations with
`sorry` are open obligations, and proofs that depend on those declarations
inherit the gap. [The audit](AUDIT.md) records the remaining obligations.

## Build

Install [Lean via Elan](https://lean-lang.org/install/) and run these commands
from the repository root. The toolchain and dependency revisions are pinned.

```sh
lake build
lake build @euclidean_jordan/EuclideanJordan
(cd vendor/euclidean-jordan && lake env lean AxiomAudit.lean)
```

For a fresh checkout, `lake exe cache get` can download prebuilt Mathlib
artifacts before the build. The default build checks both paper libraries and
all notebook modules. The second command checks the full Jordan library, and
the third checks its axiom dependencies.

[Apache License 2.0](LICENSE) · [Notice](NOTICE)
