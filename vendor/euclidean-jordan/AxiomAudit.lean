import EuclideanJordan

open Lean System

/-! # Axiom census, closure allowlist, coverage, and headline sentinels

Three layers, all enforced by elaborating this file
(`lake env lean AxiomAudit.lean` from the package root):

1. a **tracked-tree census** — over every *persisted* declaration whose defining
   module has prefix `EuclideanJordan` (this file is not visited; an anonymous
   `example := by sorry` persists no declaration and is not visited either) it
   enforces three things at once:
   (a) the axiom closure depends only on Lean's three core axioms
   (`propext`, `Classical.choice`, `Quot.sound`) — the tree carries NO custom
   axioms — so a `sorryAx`, a `native_decide`, or any other axiom fails
   elaboration; (b) NO custom axiom declaration exists in the tracked tree — any
   stray `axiom` in any tracked module fails; and
   (c) **source coverage + frozen manifest**: the set of `EuclideanJordan`
   modules on disk equals the set imported here *and* equals a pinned
   44-name manifest, so a new unimported module, a removed root import, a
   name-colliding source path, or a coordinated module+import deletion (which
   preserves `disk == imported`) fails, closing both the "invisible module" and
   the "shrink-both-sets" escapes.  The source→module map is first checked to
   reject dotted path segments and to be injective, so a file like
   `Vendor.Misc.lean` cannot collide with the nested module `Vendor/Misc`;
2. **exact-closure sentinels** — the headline results, each pinned by
   `#guard_msgs` to *exactly* the three core axioms.  The census above already
   bounds every tracked persisted declaration; these sentinels additionally
   certify that the advertised endpoints depend on the three core axioms alone,
   and they fail loudly if a headline theorem is renamed out from under the
   README;
3. **a live-carrier sentinel** — `H_n(𝕜)` really is a `EuclideanJordanAlgebra`,
   checked by instance synthesis rather than by reading the source.  Without it
   every theorem in this library would be conditional on a class with no
   instance.

The comparator `Challenge`/`Solution` pairs are *not* in the tracked tree: the
`Challenge` modules deliberately carry `sorry`, and each `Solution` is audited
by its own `#print axioms` in the Palomar entry.

## Sources

* Jacques Faraut and Adam Korányi, *Analysis on Symmetric Cones* (1994),
DOI: 10.1093/oso/9780198534778.001.0001, Theorems III.1.2 and IV.2.1 (audited spectral and Peirce results).
* Abraham Adrian Albert, *Power-associative rings* (1948),
DOI: 10.1090/S0002-9947-1948-0027750-7, Theorem 2 (commutative power associativity).
* Erik M. Alfsen and Frederic W. Shultz, *Geometry of State Spaces of Operator
Algebras* (2003), DOI: 10.1007/978-1-4612-0019-2, Theorem 2.80.
-/

-- A recursive `.lean` source enumeration for the coverage check in Layer 1(c).
partial def auditCollectLeanFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut acc : Array FilePath := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if (← p.isDir) then
      acc := acc ++ (← auditCollectLeanFiles p)
    else if p.extension == some "lean" then
      acc := acc.push p
  return acc

-- Map a source path like `EuclideanJordan/Vendor/Misc.lean` to the module name
-- `EuclideanJordan.Vendor.Misc`.
def auditPathToModule (p : FilePath) : Name :=
  let s := p.toString
  let s := if s.endsWith ".lean" then s.take (s.length - 5) else s
  (s.replace "/" ".").toName

-- Layer 1: tracked-tree census (closure allowlist + custom-axiom set + coverage).
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let citedAxioms : List Name := []
  let isProject := fun (n : Name) =>
    match env.getModuleFor? n with
    | some m => (`EuclideanJordan).isPrefixOf m
    | none => false
  -- (a) closure census + custom-axiom collection.
  let mut seenAxioms : Array Name := #[]
  let mut projectAxiomDecls : Array Name := #[]
  let mut offenders : Array Name := #[]
  let mut visited : Nat := 0
  for (n, info) in env.constants.toList do
    if isProject n then
      visited := visited + 1
      let axs ← Lean.collectAxioms n
      for a in axs do
        if !seenAxioms.contains a then
          seenAxioms := seenAxioms.push a
      if axs.any (fun a => !allowed.contains a) then
        offenders := offenders.push n
      match info with
      | .axiomInfo _ => projectAxiomDecls := projectAxiomDecls.push n
      | _ => pure ()
  -- Guard against the census silently examining nothing (an empty tracked set
  -- would pass every check below vacuously).
  if visited < 1000 then
    throwError m!"Tracked-tree census FAILED: only {visited} declarations visited; the tracked set is implausibly small (expected thousands). The module prefix or the root import is wrong."
  let bad := seenAxioms.filter (fun a => !allowed.contains a)
  if !bad.isEmpty then
    throwError m!"Tracked-tree axiom census FAILED. Unpermitted axioms: {bad}. Offending declarations: {offenders}"
  -- (b) exactly the disclosed custom-axiom set exists (here: none).
  let unexpectedAx := projectAxiomDecls.toList.filter (fun a => !citedAxioms.contains a)
  let missingAx := citedAxioms.filter (fun a => !projectAxiomDecls.contains a)
  if !unexpectedAx.isEmpty || !missingAx.isEmpty then
    throwError m!"Custom-axiom set drift. Unexpected project axioms: {unexpectedAx}. Missing disclosed axioms: {missingAx}"
  -- (c) source coverage: disk `EuclideanJordan` modules == imported ones == manifest.
  let ejDir : FilePath := "EuclideanJordan"
  unless (← ejDir.isDir) do
    throwError m!"Module-coverage gate: run from the package root ('EuclideanJordan/' not found in the current directory)"
  let files ← auditCollectLeanFiles ejDir
  -- (c0) reject malformed source paths: below the `.lean` suffix every path
  -- segment must be a single module identifier with no embedded dot.
  for p in files do
    let s := p.toString
    for seg in s.splitOn "/" do
      let dots := (seg.toList.filter (fun c => c == '.')).length
      let ok := if seg.endsWith ".lean" then dots == 1 else dots == 0
      unless ok do
        throwError m!"Module-coverage gate FAILED: source path with a dotted segment (module-name collision hazard): {p}"
  -- (c1) the source-path → module-name map must be injective on the source tree.
  let mappedMods : List Name := files.toList.map auditPathToModule
  if mappedMods.length ≠ mappedMods.eraseDups.length then
    throwError m!"Module-coverage gate FAILED: source-path→module map is not injective; distinct source files share a module name: {mappedMods}"
  let diskMods : List Name := (`EuclideanJordan :: mappedMods).eraseDups
  let importedMods : List Name :=
    (env.header.moduleNames.toList.filter (fun m => (`EuclideanJordan).isPrefixOf m)).eraseDups
  -- (c2) frozen expected-module manifest.  `disk == imported` alone is preserved
  -- by deleting a module AND its sole root import together, so the tracked
  -- surface is additionally pinned to this exact 44-name list.
  let expectedMods : List Name :=
    [`EuclideanJordan,
     `EuclideanJordan.Block,
     `EuclideanJordan.Bridge,
     `EuclideanJordan.Class,
     `EuclideanJordan.Connection,
     `EuclideanJordan.FormallyReal,
     `EuclideanJordan.Frame,
     `EuclideanJordan.FrameExists,
     `EuclideanJordan.FramePeirce,
     `EuclideanJordan.FramePeirceMul,
     `EuclideanJordan.HermitianBilin,
     `EuclideanJordan.HermitianCarrier,
     `EuclideanJordan.Order,
     `EuclideanJordan.OrderAuto,
     `EuclideanJordan.OrderUnitSpace,
     `EuclideanJordan.Orthogonal,
     `EuclideanJordan.Pattern,
     `EuclideanJordan.Peirce,
     `EuclideanJordan.PeirceMul,
     `EuclideanJordan.PeirceSubalgebra,
     `EuclideanJordan.Power,
     `EuclideanJordan.PowerAssoc,
     `EuclideanJordan.Rank,
     `EuclideanJordan.Spectral,
     `EuclideanJordan.Subalgebra,
     `EuclideanJordan.TraceForm,
     `EuclideanJordan.Vendor.ContinuousLinearMap,
     `EuclideanJordan.Vendor.HermitianMat.Basic,
     `EuclideanJordan.Vendor.HermitianMat.CFC,
     `EuclideanJordan.Vendor.HermitianMat.Inner,
     `EuclideanJordan.Vendor.HermitianMat.Jordan,
     `EuclideanJordan.Vendor.HermitianMat.NonSingular,
     `EuclideanJordan.Vendor.HermitianMat.Order,
     `EuclideanJordan.Vendor.HermitianMat.Proj,
     `EuclideanJordan.Vendor.HermitianMat.Reindex,
     `EuclideanJordan.Vendor.HermitianMat.Trace,
     `EuclideanJordan.Vendor.IsMaximalSelfAdjoint,
     `EuclideanJordan.Vendor.Isometry,
     `EuclideanJordan.Vendor.LinearEquiv,
     `EuclideanJordan.Vendor.Matrix,
     `EuclideanJordan.Vendor.Misc,
     `EuclideanJordan.Vendor.Tactic.Commutes,
     `EuclideanJordan.Vendor.Tactic.Commutes.Attribute,
     `EuclideanJordan.Witness]
  let missingOnDisk := importedMods.filter (fun m => !diskMods.contains m)
  let notImported := diskMods.filter (fun m => !importedMods.contains m)
  if !missingOnDisk.isEmpty || !notImported.isEmpty then
    throwError m!"Module-coverage gate FAILED. Imported but absent from disk: {missingOnDisk}. On disk but not imported: {notImported}"
  let manifestExtra := diskMods.filter (fun m => !expectedMods.contains m)
  let manifestMissing := expectedMods.filter (fun m => !diskMods.contains m)
  if !manifestExtra.isEmpty || !manifestMissing.isEmpty then
    throwError m!"Frozen-manifest gate FAILED. Present but not in the manifest: {manifestExtra}. In the manifest but absent: {manifestMissing}"
  logInfo m!"Layer 1 PASSED: {visited} tracked declarations, closure ⊆ 3 core axioms, 0 custom axioms, {diskMods.length} modules matching the frozen manifest."

/-! ## Layer 2: exact-closure sentinels for the headline results

Each `#guard_msgs (whitespace := lax)` fails elaboration unless the named
theorem's axiom closure is *exactly* Lean's three core axioms — and fails
outright if the name no longer exists, which is what keeps the README honest
under renaming. -/

/-- info: 'EuclideanJordan.jpow_mul_jpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.jpow_mul_jpow

/-- info: 'EuclideanJordan.jspan_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.jspan_assoc

/-- info: 'EuclideanJordan.spectral_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.spectral_resolution

/-- info: 'EuclideanJordan.spectral_resolution_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.spectral_resolution_complete

/-- info: 'EuclideanJordan.spectral_resolution_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.spectral_resolution_bilinear

/-- info: 'EuclideanJordan.traceForm_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.traceForm_assoc

/-- info: 'EuclideanJordan.traceForm_self_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.traceForm_self_eq_zero_iff

/-- info: 'EuclideanJordan.orderIso_preservesJordan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.orderIso_preservesJordan

/-- info: 'EuclideanJordan.map_jordan_of_orderIso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.map_jordan_of_orderIso

/-- info: 'EuclideanJordan.exists_jordanFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.exists_jordanFrame

/-- info: 'EuclideanJordan.frameBlock_isInternal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.frameBlock_isInternal

/-- info: 'EuclideanJordan.finrank_frameBlock_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.finrank_frameBlock_diag

/-- info: 'EuclideanJordan.orderUnitSpaceOfBilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.orderUnitSpaceOfBilinear

/-- info: 'EuclideanJordan.isArchimedean_ofBilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.isArchimedean_ofBilinear

/-- info: 'EuclideanJordan.hermitian_le_ofEJA_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EuclideanJordan.hermitian_le_ofEJA_iff

/-! ## Layer 3: the class has a live carrier

Every theorem stated over `EuclideanJordanAlgebra J` would be vacuous if the
class had no instance.  This is the check, done by synthesis rather than by
reading the source. -/

section LiveCarrier

open EuclideanJordan

noncomputable example : EuclideanJordanAlgebra (HermitianMat (Fin 3) ℂ) := inferInstance
noncomputable example : EuclideanJordanAlgebra (HermitianMat (Fin 5) ℝ) := inferInstance

/-- The `1/2`-Peirce eigenspace is genuinely inhabited on the carrier, so the
Peirce multiplication rules mentioning `J_{1/2}` are not vacuously true. -/
example : ∃ y : HermitianMat (Fin 2) ℂ, y ≠ 0 ∧ Witness.cWit * y = (2 : ℝ)⁻¹ • y :=
  Witness.witness_half_attained

end LiveCarrier
