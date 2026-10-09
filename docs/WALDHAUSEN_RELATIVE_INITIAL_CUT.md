# Actual relative-row cutoff and Reedy cofibration

## Result

For every genuine Waldhausen structure `V`, nested weak classes `N`, and
finite ordinal `n`, the original initial cutoff defines an exact functor
`cutArrow N n` into the genuine Reedy cofibration-arrow category of relative
rows. Its original transformation `cutToId N n` satisfies the structural
`Additivity.IsCofibrationTransformation` condition. The actual functor
`first N n ⋙ fiber N n` is naturally isomorphic to `cutFunctor N n`.

The seven source modules are frozen in
`logs/relative-rows-initial-cut-sources.sha256`. The structural statements
allow independent object and morphism universes. They require no saturation,
extension, cylinder, realization, or homotopy-fiber hypothesis.

## Genuine relative condition

The cutoff fixes the added initial vertex and collapses every tail vertex
to the first tail vertex. Its comparison to the original row consists of
literal original interval maps. Cofibrancy is proved on every horizontal
triple, including degenerate intervals and actual diagonal zero objects.

The arrow-valued functor requires a second, genuine cube check. The helper
`cof_cube_of_horizontal_left_isIso` derives the outer relative comparison
from actual component pushouts: its source is an isomorphism and its target
cofibration follows from the original target-face relative pushout. The
proof does not infer the Reedy condition merely from component cofibrancy.
The accepted row/arrow interchange and actual inclusion reflection then
supply `cutArrow_map_cof` and `cutArrow_exact`.

The first-object identification restricts to the actual first two vertices,
uses the zero/identity/zero natural isomorphism of genuine one-step quotient
rows, and pulls back along the actual tail collapse. Full faithfulness only
reflects that already constructed categorical isomorphism.

## Verification

All seven source modules compiled warning-free with actual Lean checks.
`audits/RelativeRowsInitialCutAudit.lean` checks every declaration by module
origin recursively against only `propext`, `Classical.choice`, and
`Quot.sound`, plus independent-universe original-map consumers.
Both the initial and final fixed77 origin audits passed warning-free; all21
actual-map consumers passed. Origin subtotals in manifest order are
9 + 2 + 14 + 14 + 4 + 21 + 13. Terminal evidence is
`logs/relative-rows-initial-cut-audit-final.log`; exact source hashes recheck
against the frozen manifest. `logs/relative-rows-initial-cut-artifacts.sha256`
records the source manifest, own audit, source-check logs, terminal audit,
and this report. Independent review is separate.

The actual quotient/cofiber and coproduct product-section are separate
companion modules. The degreewise realization equivalence is a further
assembly. The global connected-row diagonal homotopy-fiber theorem remains
an independent obligation.
