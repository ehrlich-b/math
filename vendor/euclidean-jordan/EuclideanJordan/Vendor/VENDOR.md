# Vendored code — provenance and edit record

Everything under `EuclideanJordan/Vendor/` is third-party code, retained under
its original Apache-2.0 licence with its per-file copyright headers intact. It
is not part of this library's contribution; it is the concrete carrier the
library's abstract results are instantiated on.

## physlib `HermitianMat` island

**Upstream:** [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib),
commit `a50684a191` (its "chore: Bump 4.33" commit), targeting Lean/Mathlib
**v4.33.0**. Apache-2.0; upstream author **Alex Meiburg**, with
`HermitianMat/Proj.lean` additionally **Leonardo A Lessa**.

**Why vendored rather than required as a Lake dependency:** a live dependency on
a fast-moving upstream would make this repo's zero-`sorry`, zero-custom-axiom
claim a continuous audit obligation. Vendoring pins the exact audited code.

**Files (17).** Upstream paths `QuantumInfo/ForMathlib/…` map to
`EuclideanJordan/Vendor/…`:

```
Matrix, Isometry, Misc, LinearEquiv, ContinuousLinearMap, IsMaximalSelfAdjoint,
Tactic/Commutes, Tactic/Commutes/Attribute,
HermitianMat/{Basic, Order, Inner, Trace, CFC, NonSingular, Reindex, Jordan, Proj}
```

**Edits: exactly two, both mechanical.**

1. **Import-path rewrite**, `QuantumInfo.ForMathlib` → `EuclideanJordan.Vendor`.
   Every occurrence of the string `QuantumInfo` in these files is on an import
   line, so the rewrite touches nothing else.
2. **`set_option relaxedAutoImplicit true` restored in `Matrix.lean` only**,
   marked in-file as "Vendor edit 2". This repo's `lakefile.toml` sets
   `relaxedAutoImplicit = false`, and upstream binds `dA`/`dB` as relaxed
   auto-implicits in the four Kronecker/partial-trace lemmas at
   `Matrix.lean:631-650`; without the option those 22 occurrences are unknown
   identifiers. No other vendored module needs it.

**There are no other edits** — no statement changes, no deletions, no renames,
no added helpers, no reformatting, and no `sorry`, `axiom` or `native_decide`
introduced. The upstream `module` / `public import` / `@[expose] public section`
headers are retained as-is, as are the 40
`set_option backward.isDefEq.respectTransparency false in` lines and the 3
`set_option linter.overlappingInstances false` lines.

### The `respectTransparency` lines are load-bearing — do NOT drop them

Lean v4.33 flipped `backward.isDefEq.respectTransparency`: `isDefEq` at
`.instances` transparency no longer unfolds non-reducible instance definitions.
`HermitianMat` carries two topologies —

- the `selfAdjoint` subtype topology,
  `Vendor/HermitianMat/Basic.lean:126` (`inferInstanceAs (TopologicalSpace (selfAdjoint _))`), and
- the metric topology induced by `instNormedGroup`,
  `Vendor/HermitianMat/Inner.lean:338` (`AddSubgroupClass.normedAddCommGroup _`)

— which are defeq but **not syntactically equal**. Under the new default the
elaborator stops *seeing* them as defeq, so `→L[ℝ]` gets built from one horn
while the normed-structure instances are registered against the other. Upstream
hit the same wall and reached for the compatibility knob; that is why
`Basic.lean` alone carries six of these lines. Deleting them does not produce a
clean error — it produces instance-synthesis failures and `whnf` grind in
whatever downstream file happens to trip the diamond first.

**First-party code deliberately does not use this flag.** It is a compatibility
knob slated for removal, so the first-party fix for the same diamond is an
explicit instance bridge (`EuclideanJordan/Bridge.lean`'s `ringOfBilinear`), not
the `set_option`. Inside the island the lines stay because the island stays
verbatim.

### Audit surface

The vendored modules are **tracked**: they are imported from the package root
and listed in `AxiomAudit.lean`'s frozen module manifest, so the census's
closure allowlist and custom-axiom check run over every declaration in them, not
just over the results this library consumes. Vendoring does not shrink the
audited surface.

### Standing instruction for the next toolchain bump

Re-vendor verbatim from upstream at the new pin and re-apply the two edits
above; do not patch the island in place. If a vendored lemma is needed at a
generality upstream does not state it at (for instance an `RCLike 𝕜` form of a
lemma upstream gives only over `ℂ`), state the generalization in **first-party**
code rather than editing the vendored file, so that the next re-vendor cannot
silently delete it.
