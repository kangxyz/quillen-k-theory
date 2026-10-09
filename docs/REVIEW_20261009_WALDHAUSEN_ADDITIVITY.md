# Independent acceptance: actual unbased Waldhausen additivity

Accepted 2026-10-09 after semantic inspection of all thirty implementation
sources, independent fresh rebuilds in linked isolated artifact overlays,
source-hash rechecks, and a fixed-count recursive audit of the entire combined
scope. The final audit passed all 457 declaration origins, including private
and generated declarations; only `propext`, `Classical.choice`, and `Quot.sound`
occur. Arbitrary-universe consumers verify the exact original endpoint maps,
actual cylinder formulas, and an actual acyclic-truncation application.

## The accepted theorem

For genuine Waldhausen structures V and W in the stated common-universe API,
a structural cofibration sequence of genuine exact functors F → G → H gives
an actual homotopy between the original S-realization map of G and the original
map of the pointwise coproduct H ⊔ F:

- `Waldhausen.Additivity.deloopingMap_additivity`
- `Waldhausen.Additivity.additivityHomotopy`

Chosen binary coproducts are a structural instance. Their existence is already
derived from Waldhausen zero pushouts in `Additivity.hasBinaryCoproducts`.
Neither a homotopy, an equivalence, nor additivity is supplied as an input.

## Independently checked proof

1. The actual pushout deformation retains zero diagrams, cofibration rows,
   quotient pushouts, and pointwise weak equivalences.
2. Its mixed ordinal consists of the full first copy followed by the selected
   terminal suffix of the second copy. The actual mixed cylinder retains the
   inner nerve degree. Its minimum-cut contraction is a genuine simplicial
   homotopy; zero/one endpoint identities and all ordinal restrictions are proved.
3. The two endpoint natural isomorphisms are coherent in both independent
   simplicial degrees. The nerve-direction cylinder uses genuine weak
   transformation components, preserving each actual S-row and its pushouts.
4. The original and split cofibration sequences meet at the same separated
   coproduct endpoint. The proved ordinary-subdivision realization equivalence
   cancels their precomposition. Exact diagonal naturality transports the result
   to the existing `deloopingMap`, not to a substitute map.

No based inverse of an unbased homotopy equivalence is assumed. The result is
explicitly unbased. Canonical based K-additivity, extension-category realization
equivalence, change-of-weak-equivalences fibration, Gillet–Waldhausen, strict/local
comparison and perfect localization remain separate obligations.

## Evidence

- `logs/additivity-final-independent-sources.sha256` (all thirty exact sources)
- `logs/additivity-gw-independent-check.log` (first eleven fresh source checks)
- `logs/mixed-deformation-independent-check.log` (next thirteen fresh checks)
- `logs/additivity-final-independent-check.log` (last six fresh checks)
- `audits/AdditivityFinalIndependentAudit.lean`
- `logs/additivity-final-independent-audit.log`
- `logs/additivity-final-independent-hashes.log`

Manifest SHA256:
`3b68e410d2b3957606830b51c9d60332fb5fbf95174bec9c3b408b71cc19edf5`.

The first eleven algebra sources retain four previously documented `letI`
style warnings in their first two files; the subsequent nineteen compile
warning-free. No semantic warnings, errors, or unsupported axioms remain.
The combined count is 249 additivity + 183 mixed-cylinder + 25 weak-grid origins.
A standalone weak-grid import reports 26 because `SimplexCategory.const.eq_1`
is generated there; in this combined closure it is instead attributed to the
mixed-ordinal module and counted exactly once. Exact name-list comparison
confirmed that this is the only attribution difference.
