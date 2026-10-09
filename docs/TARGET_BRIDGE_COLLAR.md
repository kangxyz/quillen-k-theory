# The original target-end open collar of a two-cylinder bridge

**Author checked, 2026-10-09 14:38:22 UTC.** Both source modules compiled
warning-free in order, followed by a successful recursive standard-axiom
scan of all **94 = 37 + 57** defining origins and **27 actual-map consumers**.
A fixed-94 guard is installed for independent replay. Independent review is
pending; no redundant author replay is queued.

Frozen source manifest: `logs/target-bridge-collar-sources.sha256`, fingerprint
`cfac84c06a08adccf6bd39a696068ff4adc1aab70aac968bcc2df2d018e314ab`.

## Actual geometry

For an original displayed mapping cylinder of `f : A → B`, height is the
original interval coordinate on the cylinder leg and constant one on the
target leg. The pushout relation at the terminal endpoint makes this an
actual continuous map. The source end has height zero.

The original target strong deformation changes height by the exact formula
`intervalSlide (symm t) h`. This is at least the original height. Consequently
it restricts to the unchanged subspace `{cut < height}` for every `cut : I`
with `cut < 1`. Its retraction is literally the original mapping-cylinder
projection on that subspace, and its deformation is the original deformation
restricted to it. It fixes the whole target and preserves every base map
induced from that target. The attaching map is arbitrary.

For two actual mapping cylinders glued along their source ends, height is
this first-cylinder height and zero on the entire second cylinder. These
agree on the common source. The positive collar is an actual open subset of
the glued bridge. Restricting the displayed pushout to this open subset makes
the second corner empty, since `cut ≥ 0`. The restricted left inclusion is an
actual homeomorphism, proved from the original restricted pushout universal
property and its empty right corner. No injective attaching map or abstract
fiber/pushout interchange is used.

Transporting the restricted target SDR through that homeomorphism gives a
genuine SDR of the bridge collar onto the original first target. The original
inclusion is retained literally, and the full homotopy preserves the original
`FiberwiseBridge.projection`. No equivalence, weak-equivalence, HLP, or HELP
assumption on either attaching map appears.

## Importable API

Import `Quillen.CategoryTheory.TheoremB.FiberwiseBridgeTargetCollar`.

The generic namespaces are:

- `Quillen.TheoremB.MappingCylinderTargetCollar`: `height`, exact cylinder/
  target/source and deformation formulas, `Collar`, `target`,
  `strongDeformationRetract`, `deformation_over`.
- `Quillen.TheoremB.FiberwiseBridgeTargetCollar`: `height`, `height_left`,
  `height_right`, `height_target`, `collarHomeomorph`, `Collar`, `target`,
  `strongDeformationRetract`, `deformation_over`.

For the unchanged `NormalizedFibrationSpan.Data d`, the exact wrappers are:

- `d.bridgeTargetHeight`, with `_left`, `_right`, `_target` formulas;
- `d.BridgeTargetCollar cut` and `d.bridgeTargetCollar_isOpen cut`;
- `d.bridgeTargetCollarTarget cut hc` and
  `d.bridgeTargetCollarInclusion cut`;
- `d.bridgeTargetCollarTarget_inclusion`: their composite is definitionally
  the original `d.normalized.i0`;
- `d.bridgeTargetCollarSDR cut hc`;
- `d.bridgeTargetCollarSDR_over`: its full cylinder homotopy preserves the
  original `d.bridgeProjection` after the literal subspace inclusion.

All categories and parameter spaces here share the explicit arbitrary
universe `u`. Bounds are `cut : unitInterval`, hence `0 ≤ cut ≤ 1`, plus
`hc : cut < 1`. The endpoint `cut = 0` is included. Empty spaces require no
special nonemptiness assumption.

## Verification

- Sources: `MappingCylinderTargetCollar.lean` (118 lines) and
  `FiberwiseBridgeTargetCollar.lean` (207 lines), under
  `Quillen/CategoryTheory/TheoremB/`.
- Audit: `audits/TargetBridgeCollarAudit.lean`.
- Replay script: `logs/verify-target-bridge-collar.sh`.
- Successful author replay: `logs/target-bridge-collar-audit-initial.log`.
- Evidence: `logs/target-bridge-collar-artifacts.sha256`.

The single-pass recursive audit allows only `propext`, `Classical.choice`,
and `Quot.sound`. The 27 consumers retain original height and deformation
coordinates, both actual collar homeomorphism directions, target inclusion
and retraction, the exact fiberwise equation, normalized wrappers, empty
target behavior and the zero cutoff. The initial source diagnostics were
ordinary forget-map transparency, an empty-space continuity spelling, and
one endpoint rewrite; they were resolved without changing the mathematical
scope. All final production and consumer checks are warning-free.

## Remaining step

This boundary gives the real open collar inside the bridge. Pushing it into
an open neighborhood of the first normalized attachment, proving its
complement-fiber formula, and the finite weak-gluing theorem remain separate
work. No full-bridge equivalence or global fibration conclusion is asserted.
This is post-freeze work outside the immutable 12:10 checkpoint.
