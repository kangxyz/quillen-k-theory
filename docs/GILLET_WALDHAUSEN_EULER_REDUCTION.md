# Actual finite and global degree-zero reduction

This work is a new boundary after the accepted finite-cycle and based-coverage
constructions. It retains the original inherited isomorphism weak models.
The genuine quasi-isomorphism fibration remains a separate proof obligation.

## Finite reduction

`FiniteEulerReduction.lean` transports only the stated integer upper bound
of the accepted finite term equivalence. Its forward maps remain the
original term-evaluation KMaps. For the actual closed interval `[a,a+m]`,
`finiteTermKEquivClosed_incidence` identifies the original acyclic-inclusion
KMap with the literal accepted adjacent-incidence homomorphism on the
proved cycle coordinates. This includes both unit boundary coordinates,
including m=0. `finiteTermKEquivClosed_single` identifies original insertion
at any allowed degree with the literal `Pi.mulSingle` map.

`finiteTerm_existsUnique_acyclic_single` then transfers the independently
proved finite group calculation to actual K-classes: every termwise class
in that interval has a unique actual acyclic class times a unique actual
single-term class in any specified allowed degree. There is no formal
coordinate-map or equivalence hypothesis.

## Global reduction

`GlobalEulerReduction.lean` defines the original mathlib single-complex
functor into the actual bounded termwise category and proves its exactness,
actual map formula, and canonical KMap compatibility with finite inclusions
and increasing transitions. These single-insertion statements do not need
kernel closure.

For the actual symmetric interval `[-N,N]`, integer arithmetic identifies
the true degree-zero term with coordinate N among `2N+1` terms. The finite
reduction is applied at this coordinate, rather than at the interval's
initial degree. Actual based finite-stage representation gives a global
representation as original acyclic-inclusion image times original
single-in-degree-zero image. Eventual equality detection and the finite
uniqueness theorem detect the joint kernel and prove uniqueness globally.

The proved endpoint is `boundedTerms_existsUnique_acyclic_single_zero` in
every original K-group, including K₀. The acyclic component is an actual
class in the nontrivial isomorphism-model acyclic K-group; it is not discarded
or assumed to vanish.

## Hypotheses and scope

A is abelian, with the honest compatible mixed universe
`A : Type (max u v)` and `Category.{v} A`. P contains zero, is replete,
extension-closed, and structurally kernel-closed for cycle statements.
No global term bound, global projectivity, resolution property, global
graded equivalence, or fibration conclusion is an input. Arbitrary schemes
use the already proved finite-locally-free ambient kernel-closure instance.

## Verification status

Both focused source builds passed warning-free. The frozen source manifest is
`logs/gillet-waldhausen-euler-reduction-checked-sources.sha256`.
The finite-only driver `audits/GilletWaldhausenFiniteEulerAudit.lean` passed
its fixed25 origin audit and explicit original-coordinate/m=0/K₀/arbitrary-scheme
consumers, with log `logs/gillet-waldhausen-finite-euler-axioms.log`.

The aggregate driver `audits/GilletWaldhausenEulerReductionAudit.lean` passed
its fixed1081 recursive audit and the full earlier/current consumer suite,
including the actual global unique-representation theorem on arbitrary
schemes. New origins are 25 finite and 34 global. The terminal raw log is
`logs/gillet-waldhausen-euler-reduction-axioms.log`. There are no warnings,
errors, or `sorryAx`; all recursive assumptions are the standard `propext`,
`Classical.choice`, and `Quot.sound`. The actual scheme consumer explicitly
annotates both the main theorem and the mixed-universe single exact functor
with `{u,u+1}`; the finite inclusion uses the same annotation.

All two plus prior forty-seven frozen source hashes match. Artifact evidence
is `logs/gillet-waldhausen-euler-reduction-artifacts.sha256` and the prior hash
log is `logs/gillet-waldhausen-euler-reduction-prior-hashes.log`.
Independent review passed a fresh two-target overlay rebuild, fixed59
recursive new origins, and 16 strengthened original-map/finite/global/K₀/
arbitrary-scheme consumers. It is recorded in
`docs/REVIEW_20261009_GW_EULER_REDUCTION.md`. The later single/change-of-weak triangle is
being developed separately and is not part of this frozen two-source boundary.
