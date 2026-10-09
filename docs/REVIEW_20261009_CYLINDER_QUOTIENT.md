# Independent review: actual relative complex-cylinder quotient

Verdict: accepted. Both fresh source rebuilds were warning-free; all 25 origins
and every independent consumer passed. Before/after source and inspected-dependency
hashes matched.

Scope: the two frozen sources in `logs/cylinder-quotient-sources.sha256`:

- `Quillen/Waldhausen/Cylinder/RelativeQuotient.lean`
- `Quillen/Waldhausen/Cylinder/ComplexQuotient.lean`

## Semantic review

The general categorical lemma proves the requested cokernel universal property;
it does not take that property as a hypothesis. Given an arrow out of the target
middle object annihilating the relative map, its composite with the target left
arrow vanishes by the displayed commuting square. The actual target cokernel
therefore gives a first descent. The source quotient is epimorphic, so the other
commuting square proves that this first descent annihilates the map on quotient
objects. The actual cokernel of that quotient map gives the second descent.
The two original cokernel uniqueness properties prove uniqueness of the final
descent. No relative pushout universal property is used or concealed at this
stage: the displayed zero composite and two commuting legs suffice.

In the complex application, the displayed quotient object is definitionally
`(cokernel alpha.left)[1]`, and its projection is definitionally the original
joint cylinder projection followed by the shifted actual cokernel projection.
The relative pushout is used to prove the required zero composite by checking
both pushout legs. Naturality of the genuine joint quotient sequence and the
cokernel equation discharge those two checks. The shift functor preserves the
actual cokernel universal property, and the source joint quotient is epi because
its independently constructed joint sequence is short exact.

The short-exactness theorem adds only degreewise split monicity of `alpha.left`.
Its monomorphism conclusion is obtained from the existing explicit relative
retraction theorem, applied degreewise to the genuine joint sequence splittings.
The quotient map is epi and the sequence is exact from the newly proved cokernel
universal property. A condition on `alpha.right` is not needed here. This is
consistent with the actual quotient being determined solely by the source map.

I also read the relevant dependencies: `RelativeComplex`, `RelativeSplitMono`,
`JointEndpoints`, and `FunctorialFactorization`. They use the identity-cone
factorization, actual biproduct endpoint maps, explicit degreewise splittings,
and pushout universal properties. These dependencies were hashed before and
after the check.

## Scope boundaries

The theorem is valid for cochain complexes over an arbitrary abelian category,
with independent object and hom universes. The generic cokernel lemma needs
only a category with zero morphisms and its explicit universal-property data.
There is no assumption of the desired relative cokernel conclusion, no
cross-universe realization claim, and no new axiom.

This scope does not prove membership of the quotient in a bounded or perfect
subcategory, chosen-zero normalization, a full Waldhausen cylinder structure,
fibration, or a Gillet–Waldhausen equivalence.

## Verification evidence

Both exact frozen sources were rebuilt into a fresh independent output overlay,
without changing live implementation sources or outputs. Dependencies in that
overlay link to existing accepted artifacts; the two reviewed leaf outputs are
new regular files. `import-resolution.log` verifies that the second source and
independent audit import the freshly rebuilt reviewed modules.

`audits/Review20261009CylinderQuotientAudit.lean` checks every one of the fixed
25 declaration origins recursively, including generated/private declarations,
against only `propext`, `Classical.choice`, and `Quot.sound`. In addition to the
author's consumers, independent examples check all three displayed objects,
the exact quotient projection, its derived zero composite, degreewise splitting
with only the source condition, and the minimal nonabelian categorical cokernel
interface. Object/hom universes remain independent in these consumers.

Detailed evidence is under `logs/cylinder-quotient-independent-20261009/`.
