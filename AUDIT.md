# Release audit

## Privacy

Scanned the release file names and UTF-8 contents for credential formats,
credential assignments, email addresses, private network addresses and host
names, home and service paths, and employer references. The scan found no
credentials or personal contact details in the retained files.

| Finding | Resolution |
| --- | --- |
| `original/papers/PaperA/Definitions.lean` contained a private-work label. | Removed the label from the module introduction. |
| `original/musings/RationalClockStatements.lean` referred to two private notebook records. | Removed the two references. The statement still points readers to the Lean proofs. |
| The source checkout's prior commits contain author contact metadata. | The release starts at a single root commit and uses GitHub's noreply address for its author and committer. |

[EXCLUDED.md](EXCLUDED.md) lists each omitted input path. Those files were
excluded as a group from the public build and its history.

## Licenses and provenance

| Included files | Provenance and license |
| --- | --- |
| `original/papers/**/*.lean` and `original/musings/*.lean` | Matched to formal sources authored by Bryan Ehrlich with AI assistance. This release applies Apache-2.0. Local changes affect imports, documentation and whitespace. |
| `vendor/euclidean-jordan/EuclideanJordan/Vendor/**/*.lean` | All 17 files checked against the pinned physlib sources. The differences are the recorded import relocation and one compatibility option. Existing Apache-2.0 headers and named authors remain. |
| Remaining `vendor/euclidean-jordan/` files | Bryan Ehrlich’s Apache-2.0 Jordan library, its license, upstream code record, package settings and audit. The release adds citations and a notice, replaces the README and removes comparator targets. |
| Lake config, manifest and toolchain | Package configuration and dependency pins. The manifest retains Mathlib, its transitive dependencies, and the local Jordan package. External dependency source stays in its own repository. |
| Release README files, notices, inventories, license and ignore file | Written for this release or, for the license text, carried from the Jordan package. Apache-2.0. |

The retained source contains no detected share-alike or noncommercial code.
The mathematical references are citations, and the release includes no
copies of the cited books or manuscripts.

## Original notebook and published mathematics

| File in `original/musings/` | Reason for inclusion as original work |
| --- | --- |
| [`BMO5TrapDepth.lean`](original/musings/BMO5TrapDepth.lean) | Proves a stopping-depth result for the shifted recurrence, extending Problem 5 with a different claim. |
| [`BMO5TrapDepthAudit.lean`](original/musings/BMO5TrapDepthAudit.lean) | Reports the axiom closures of the stopping-depth and recurrence-bridge results. |
| [`ObserverCapacity.lean`](original/musings/ObserverCapacity.lean) | Proves the finite-memory survival bound and its joint-initial-state extension. |
| [`ObserverCapacityAudit.lean`](original/musings/ObserverCapacityAudit.lean) | Reports the axiom closures of the observer bounds and examples. |
| [`ObserverCapacityInitialExamples.lean`](original/musings/ObserverCapacityInitialExamples.lean) | Proves small examples that show how initial memory changes the bound. |
| [`README.md`](original/musings/README.md) | States the scope and review status of Bryan Ehrlich’s notebook results. |
| [`RationalClockAxiomAudit.lean`](original/musings/RationalClockAxiomAudit.lean) | Reports the axiom closures of the classification and 2-adic results. |
| [`RationalClockBackward.lean`](original/musings/RationalClockBackward.lean) | Transports congruences and clocks backwards in the recurrence. |
| [`RationalClockBasic.lean`](original/musings/RationalClockBasic.lean) | Proves low-part and ruler-sum facts for the notebook recurrence. |
| [`RationalClockBound.lean`](original/musings/RationalClockBound.lean) | Bounds the finite discrepancy in a periodic clock. |
| [`RationalClockClassification.lean`](original/musings/RationalClockClassification.lean) | Proves the exact class lists for the two specified coefficients. |
| [`RationalClockConsequences.lean`](original/musings/RationalClockConsequences.lean) | Computes the valuation clocks and exact power-of-two hits. |
| [`RationalClockDynamics.lean`](original/musings/RationalClockDynamics.lean) | Transports rational clocks along positive orbits. |
| [`RationalClockGeneral.lean`](original/musings/RationalClockGeneral.lean) | Proves the uniform finite bound on rational-clock classes. |
| [`RationalClockInteger.lean`](original/musings/RationalClockInteger.lean) | Handles integer clocks by finite binary complementation. |
| [`RationalClockIsometry.lean`](original/musings/RationalClockIsometry.lean) | Establishes the isometry of finite binary clocks. |
| [`RationalClockPadic.lean`](original/musings/RationalClockPadic.lean) | Constructs the 2-adic clock and conjugacy. |
| [`RationalClockPadicMeasure.lean`](original/musings/RationalClockPadicMeasure.lean) | Proves residue counts, Haar invariance, ergodicity, and uniqueness. |
| [`RationalClockPadicRational.lean`](original/musings/RationalClockPadicRational.lean) | Identifies rational points in the 2-adic clock model. |
| [`RationalClockPeriodic.lean`](original/musings/RationalClockPeriodic.lean) | Evaluates finite repeated clock blocks. |
| [`RationalClockPhase.lean`](original/musings/RationalClockPhase.lean) | Reduces rational interior phases to repeated blocks and bounds them. |
| [`RationalClockRepresentation.lean`](original/musings/RationalClockRepresentation.lean) | Proves clock uniqueness and endpoint values. |
| [`RationalClockResearch.lean`](original/musings/RationalClockResearch.lean) | Collects the notebook classification and 2-adic endpoints. |
| [`RationalClockShift.lean`](original/musings/RationalClockShift.lean) | Proves signed integer shift formulas for rational clocks. |
| [`RationalClockStatements.lean`](original/musings/RationalClockStatements.lean) | Defines the notebook recurrence and states the classification claims. |
| [`RationalClockValuation.lean`](original/musings/RationalClockValuation.lean) | Connects valuations with the orbit from one. |

| File in `formalized/` | Role |
| --- | --- |
| [`proofs/README.md`](formalized/proofs/README.md) | Describes how to file future proofs with source citations and receipts. |

The classical Jordan algebra formalizations are under
[vendor/euclidean-jordan](vendor/euclidean-jordan/). The separate notice covers
the bundled library and its physlib supporting modules. The published sources
are indexed in [ATTRIBUTION.md](ATTRIBUTION.md).

## Build check

On 2026-11-21, `lake build`, `lake build @euclidean_jordan/EuclideanJordan`,
and the Jordan `AxiomAudit.lean` check each exited successfully with Lean
4.33.0. The build ran in a fresh Linux scratch directory in the batch
resource slice, using the cached packages at the manifest revisions. The
shared cache has a local edit to Mathlib's umbrella module. The release
imports the required upstream modules directly.

The Jordan axiom census checked 1,841 declarations in 44 modules and found
only Lean's three core axioms. All 19 notebook axiom checks were within the
same allowlist, including the rational-clock classification and quantitative
2-adic results. The paper build emitted 98 placeholder warnings, all listed
below. The build also emitted linter warnings.

## Open proof obligations

There are 98 explicit proof placeholders in the two paper libraries.
Any proof depending on one of these declarations also depends on `sorryAx`.

| Declaration | Placeholder location |
| --- | --- |
| `restrictProducts` | [`original/papers/PaperA/Assembly.lean:152`](original/papers/PaperA/Assembly.lean#L152) |
| `frame_rank` | [`original/papers/PaperA/Claims.lean:94`](original/papers/PaperA/Claims.lean#L94) |
| `frame_conjugacy` | [`original/papers/PaperA/Claims.lean:98`](original/papers/PaperA/Claims.lean#L98) |
| `sqrt_spec` | [`original/papers/PaperA/Claims.lean:202`](original/papers/PaperA/Claims.lean#L202) |
| `sqrt_continuous` | [`original/papers/PaperA/Claims.lean:206`](original/papers/PaperA/Claims.lean#L206) |
| `q_order_inverse` | [`original/papers/PaperA/Claims.lean:210`](original/papers/PaperA/Claims.lean#L210) |
| `order_auto_jordan` | [`original/papers/PaperA/Claims.lean:218`](original/papers/PaperA/Claims.lean#L218) |
| `left_norm` | [`original/papers/PaperA/Claims.lean:789`](original/papers/PaperA/Claims.lean#L789) |
| `scalars` | [`original/papers/PaperA/Claims.lean:793`](original/papers/PaperA/Claims.lean#L793) |
| `continuity` | [`original/papers/PaperA/Claims.lean:797`](original/papers/PaperA/Claims.lean#L797) |
| `frame_calculus` | [`original/papers/PaperA/Claims.lean:895`](original/papers/PaperA/Claims.lean#L895) |
| `positive_inverse` | [`original/papers/PaperA/Claims.lean:899`](original/papers/PaperA/Claims.lean#L899) |
| `theta_auto` | [`original/papers/PaperA/Claims.lean:903`](original/papers/PaperA/Claims.lean#L903) |
| `theta_fix` | [`original/papers/PaperA/Claims.lean:907`](original/papers/PaperA/Claims.lean#L907) |
| `theta_continuous` | [`original/papers/PaperA/Claims.lean:911`](original/papers/PaperA/Claims.lean#L911) |
| `theta_cocycle` | [`original/papers/PaperA/Claims.lean:915`](original/papers/PaperA/Claims.lean#L915) |
| `coalescence` | [`original/papers/PaperA/Claims.lean:919`](original/papers/PaperA/Claims.lean#L919) |
| `frame_fix` | [`original/papers/PaperA/Claims.lean:923`](original/papers/PaperA/Claims.lean#L923) |
| `homomorphism` | [`original/papers/PaperA/Claims.lean:927`](original/papers/PaperA/Claims.lean#L927) |
| `per_frame_rigid` | [`original/papers/PaperA/Claims.lean:1062`](original/papers/PaperA/Claims.lean#L1062) |
| `per_frame_complex` | [`original/papers/PaperA/Claims.lean:1066`](original/papers/PaperA/Claims.lean#L1066) |
| `adjacent` | [`original/papers/PaperA/Claims.lean:1141`](original/papers/PaperA/Claims.lean#L1141) |
| `frame_connectivity` | [`original/papers/PaperA/Claims.lean:1145`](original/papers/PaperA/Claims.lean#L1145) |
| `singular_luders` | [`original/papers/PaperA/Claims.lean:1149`](original/papers/PaperA/Claims.lean#L1149) |
| `singular_twist` | [`original/papers/PaperA/Claims.lean:1153`](original/papers/PaperA/Claims.lean#L1153) |
| `complex_classification` | [`original/papers/PaperA/Claims.lean:1157`](original/papers/PaperA/Claims.lean#L1157) |
| `twist_sufficiency` | [`original/papers/PaperA/Claims.lean:1161`](original/papers/PaperA/Claims.lean#L1161) |
| `luders_sufficiency` | [`original/papers/PaperA/Claims.lean:1165`](original/papers/PaperA/Claims.lean#L1165) |
| `spin_generator_continuous` | [`original/papers/PaperA/Claims.lean:1290`](original/papers/PaperA/Claims.lean#L1290) |
| `spin_sufficiency` | [`original/papers/PaperA/Claims.lean:1294`](original/papers/PaperA/Claims.lean#L1294) |
| `spin_classification` | [`original/papers/PaperA/Claims.lean:1298`](original/papers/PaperA/Claims.lean#L1298) |
| `qubit_classification` | [`original/papers/PaperA/Claims.lean:1371`](original/papers/PaperA/Claims.lean#L1371) |
| `rigid` | [`original/papers/PaperA/Claims.lean:1407`](original/papers/PaperA/Claims.lean#L1407) |
| `rank_one` | [`original/papers/PaperA/Claims.lean:1411`](original/papers/PaperA/Claims.lean#L1411) |
| `jvnw` | [`original/papers/PaperA/Claims.lean:1415`](original/papers/PaperA/Claims.lean#L1415) |
| `central` | [`original/papers/PaperA/Claims.lean:1423`](original/papers/PaperA/Claims.lean#L1423) |
| `master` | [`original/papers/PaperA/Claims.lean:1427`](original/papers/PaperA/Claims.lean#L1427) |
| `simple_parametrization` | [`original/papers/PaperA/Claims.lean:1431`](original/papers/PaperA/Claims.lean#L1431) |
| `omnibus` | [`original/papers/PaperA/Claims.lean:1435`](original/papers/PaperA/Claims.lean#L1435) |
| `dyn_equivalence` | [`original/papers/PaperA/Claims.lean:1439`](original/papers/PaperA/Claims.lean#L1439) |
| `dyn_form` | [`original/papers/PaperA/Claims.lean:1443`](original/papers/PaperA/Claims.lean#L1443) |
| `dyn_rank_two` | [`original/papers/PaperA/Claims.lean:1447`](original/papers/PaperA/Claims.lean#L1447) |
| `sharp` | [`original/papers/PaperA/Claims.lean:1451`](original/papers/PaperA/Claims.lean#L1451) |
| `moduli` | [`original/papers/PaperA/Claims.lean:1516`](original/papers/PaperA/Claims.lean#L1516) |
| `selectors_trace` | [`original/papers/PaperA/Claims.lean:1520`](original/papers/PaperA/Claims.lean#L1520) |
| `selectors_transpose` | [`original/papers/PaperA/Claims.lean:1549`](original/papers/PaperA/Claims.lean#L1549) |
| `vdw_reconstruction` | [`original/papers/PaperA/Claims.lean:1553`](original/papers/PaperA/Claims.lean#L1553) |
| `inverse_sqrt_continuous` | [`original/papers/PaperA/Claims.lean:1557`](original/papers/PaperA/Claims.lean#L1557) |
| `principal_skew_log` | [`original/papers/PaperA/Claims.lean:1995`](original/papers/PaperA/Claims.lean#L1995) |
| `spin_s4` | [`original/papers/PaperA/Claims.lean:2003`](original/papers/PaperA/Claims.lean#L2003) |
| `spin_s5` | [`original/papers/PaperA/Claims.lean:2007`](original/papers/PaperA/Claims.lean#L2007) |
| `twist_transpose` | [`original/papers/PaperA/Claims.lean:2027`](original/papers/PaperA/Claims.lean#L2027) |
| `composition` | [`original/papers/PaperA/Claims.lean:2031`](original/papers/PaperA/Claims.lean#L2031) |
| `twist_weak_selectors` | [`original/papers/PaperA/Claims.lean:2035`](original/papers/PaperA/Claims.lean#L2035) |
| `aut_compact` | [`original/papers/PaperA/Claims.lean:2189`](original/papers/PaperA/Claims.lean#L2189) |
| `model_inhabitance` | [`original/papers/PaperA/Claims.lean:2216`](original/papers/PaperA/Claims.lean#L2216) |
| `spin_low_rank_models` | [`original/papers/PaperA/Claims.lean:2220`](original/papers/PaperA/Claims.lean#L2220) |
| `spin_s67` | [`original/papers/PaperA/Claims.lean:2228`](original/papers/PaperA/Claims.lean#L2228) |
| `matrix_aut_types` | [`original/papers/PaperA/Claims.lean:2232`](original/papers/PaperA/Claims.lean#L2232) |
| `unitary_covariance` | [`original/papers/PaperA/Claims.lean:2236`](original/papers/PaperA/Claims.lean#L2236) |
| `atomic_transition_symmetry` | [`original/papers/PaperA/Claims.lean:2240`](original/papers/PaperA/Claims.lean#L2240) |
| `central_coordinate_generator` | [`original/papers/PaperA/Claims.lean:2258`](original/papers/PaperA/Claims.lean#L2258) |
| `trace_form` | [`original/papers/PaperA/Claims.lean:2262`](original/papers/PaperA/Claims.lean#L2262) |
| `support_unitary` | [`original/papers/PaperA/Claims.lean:2266`](original/papers/PaperA/Claims.lean#L2266) |
| `backaction` | [`original/papers/PaperA/Claims.lean:2270`](original/papers/PaperA/Claims.lean#L2270) |
| `moduli_isomorphism` | [`original/papers/PaperA/Claims.lean:2274`](original/papers/PaperA/Claims.lean#L2274) |
| `frame_nonconjugacy` | [`original/papers/PaperA/Claims.lean:2294`](original/papers/PaperA/Claims.lean#L2294) |
| `spin_zero_luders` | [`original/papers/PaperA/Claims.lean:2298`](original/papers/PaperA/Claims.lean#L2298) |
| `qubit_pauli_twist` | [`original/papers/PaperA/Claims.lean:2310`](original/papers/PaperA/Claims.lean#L2310) |
| `compact_lie_identification` | [`original/papers/PaperA/Spec/ModelsLie.lean:155`](original/papers/PaperA/Spec/ModelsLie.lean#L155) |
| `one_parameter_derivation` | [`original/papers/PaperA/Spec/ModelsLie.lean:180`](original/papers/PaperA/Spec/ModelsLie.lean#L180) |
| `peirce_dimensions_equal` | [`original/papers/PaperA/Spec/ModelsLie.lean:230`](original/papers/PaperA/Spec/ModelsLie.lean#L230) |
| `real_peirce_dimension` | [`original/papers/PaperA/Spec/ModelsLie.lean:250`](original/papers/PaperA/Spec/ModelsLie.lean#L250) |
| `complex_peirce_dimension` | [`original/papers/PaperA/Spec/ModelsLie.lean:270`](original/papers/PaperA/Spec/ModelsLie.lean#L270) |
| `quaternion_peirce_dimension` | [`original/papers/PaperA/Spec/ModelsLie.lean:290`](original/papers/PaperA/Spec/ModelsLie.lean#L290) |
| `albert_peirce_dimension` | [`original/papers/PaperA/Spec/ModelsLie.lean:310`](original/papers/PaperA/Spec/ModelsLie.lean#L310) |
| `model_rank` | [`original/papers/PaperA/Spec/ModelsLie.lean:351`](original/papers/PaperA/Spec/ModelsLie.lean#L351) |
| `composition_family` | [`original/papers/PaperA/Spec/Observations.lean:186`](original/papers/PaperA/Spec/Observations.lean#L186) |
| `peirce_action_formula` | [`original/papers/PaperA/Spec/Observations.lean:296`](original/papers/PaperA/Spec/Observations.lean#L296) |
| `peirce_exchange_character` | [`original/papers/PaperA/Spec/Observations.lean:316`](original/papers/PaperA/Spec/Observations.lean#L316) |
| `selectors_peirce_exchange` | [`original/papers/PaperA/Spec/Observations.lean:333`](original/papers/PaperA/Spec/Observations.lean#L333) |
| `selectors_order_covariant` | [`original/papers/PaperA/Spec/Observations.lean:381`](original/papers/PaperA/Spec/Observations.lean#L381) |
| `composition_family_distinct` | [`original/papers/PaperA/Spec/Observations.lean:470`](original/papers/PaperA/Spec/Observations.lean#L470) |
| `positive_extension` | [`original/papers/PaperA/Spec/SpinNecessity.lean:71`](original/papers/PaperA/Spec/SpinNecessity.lean#L71) |
| `frame_generator` | [`original/papers/PaperA/Spec/SpinNecessity.lean:107`](original/papers/PaperA/Spec/SpinNecessity.lean#L107) |
| `reversal_uniqueness` | [`original/papers/PaperA/Spec/SpinNecessity.lean:121`](original/papers/PaperA/Spec/SpinNecessity.lean#L121) |
| `scalar_approach` | [`original/papers/PaperA/Spec/SpinNecessity.lean:143`](original/papers/PaperA/Spec/SpinNecessity.lean#L143) |
| `product_uniform_small` | [`original/papers/PaperA/Spec/SpinNecessity.lean:165`](original/papers/PaperA/Spec/SpinNecessity.lean#L165) |
| `maximal_frequency` | [`original/papers/PaperA/Spec/SpinNecessity.lean:186`](original/papers/PaperA/Spec/SpinNecessity.lean#L186) |
| `principal_log_reconstruction` | [`original/papers/PaperA/Spec/SpinNecessity.lean:237`](original/papers/PaperA/Spec/SpinNecessity.lean#L237) |
| `singular_multipliers` | [`original/papers/PaperA/Spec/SpinNecessity.lean:276`](original/papers/PaperA/Spec/SpinNecessity.lean#L276) |
| `boundary_agreement` | [`original/papers/PaperA/Spec/SpinNecessity.lean:300`](original/papers/PaperA/Spec/SpinNecessity.lean#L300) |
| `paperA` | [`original/papers/PaperA/Statement.lean:678`](original/papers/PaperA/Statement.lean#L678) |
| `paperB` | [`original/papers/PaperB/Statement.lean:170`](original/papers/PaperB/Statement.lean#L170) |
| `homogeneous_of_HE` | [`original/papers/PaperB/Statement.lean:176`](original/papers/PaperB/Statement.lean#L176) |
| `rankTwo_HE_iff_lorentz` | [`original/papers/PaperB/Statement.lean:193`](original/papers/PaperB/Statement.lean#L193) |
| `spinFactor_satisfies_HE` | [`original/papers/PaperB/Statement.lean:199`](original/papers/PaperB/Statement.lean#L199) |
| `asymmetricCone_fails_HE` | [`original/papers/PaperB/Statement.lean:221`](original/papers/PaperB/Statement.lean#L221) |
