# Full contracted compact HELP over the displayed base

Checked 2026-10-09. This boundary comprises exactly the three sources in
`logs/full-over-base-sources.sha256`.

## Actual endpoint

`Quillen.fullHELP_over_contracted_test` starts with genuine HLP projections
`p : E → B`, `q : F → B`, an actual map `f : E → F` with `q ∘ f = p`,
and full compact HELP on every original strict-fiber map. Its test is an
actual compact HEP pair `i : A → D`, an explicit contraction of `D`, and a
continuous interval-valued duration with zero locus exactly the image of `i`.

For an arbitrary prescribed boundary homotopy `H : f ∘ a ~ b ∘ i` lying over
`q ∘ b ∘ i`, it constructs `c : D → E` and `V : f ∘ c ~ b` such that:

- `c ∘ i = a` exactly;
- `p ∘ c = q ∘ b` exactly;
- `q(V(t,x)) = q(b(x))` for every time and parameter;
- `V(t,i(x)) = H(t,x)` for every time and boundary point.

Both endpoint maps and the entire originally prescribed, possibly nonconstant
boundary track are retained. No arbitrary-test compact HELP or global fiber
comparison is asserted.

## Proof ingredients

`HomotopyLiftingProperty.extend_over_fixed_base` first performs ordinary HEP,
then corrects the projected reverse-time path using stationary HLP with
vanishing duration `t*d(x)`. This fixes the full prescribed track and time zero.

`correct_boundary_over_fixed_base` uses the genuine interval-square HEP
extension, corrected with duration `s*t*(1-t)*d(x)`. It retains the initial
square, both path endpoints and every prescribed boundary value.
`unpad_boundary_over_fixed_base` specializes this to the actual constant-prefix
path deformation. The final theorem composes these constructions with the
previously accepted strict over-base HELP.

## Author validation

All three frozen sources were checked in dependency order, warning-free.
`audits/FullOverBaseHELPAudit.lean` recursively audits all seven defining-module
origins, including generated proof helpers, with a fixed-count guard. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Its five consumers include
the full exact theorem signatures and the actual arbitrary-dimensional lifted
cube with its entire original boundary and pointwise base equation.

- Ordered source and initial scan: `logs/full-over-base-initial.log`
- Fixed-seven audit and consumers: `logs/full-over-base-fixed7.log`
- Frozen sources: `logs/full-over-base-sources.sha256`
- Validation script: `logs/verify-full-over-base.sh`

Independent review is recorded separately by its reviewer.
