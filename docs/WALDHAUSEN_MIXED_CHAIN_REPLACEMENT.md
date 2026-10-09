# Original finite-chain cylinder replacement

## Generic structural endpoint

`Fibration.MixedChainReplacement` reuses the existing actual functor
`FunctorialFactorization.finiteReplacement D n` on `ComposableArrows C n`.
It introduces no replacement object choice and no comparison equivalence.

Inputs are a genuine nested fine/coarse Waldhausen structure `N`, the
already-structural functorial cofibration/coarse-weak factorization `D`, and,
for preservation of fine morphisms, `PreservesFineSquares N D`. The latter
says exactly that the actual middle functor sends a square with fine-weak
left and right sides to a fine-weak map. It has no homotopical conclusion.

Theorems prove:

- Every replacement arrow is a fine cofibration, using the actual equality
  of the fine and coarse cofibration classes.
- Under coarse two-out-of-three, each originally coarse-weak arrow remains
  coarse-weak. The proof uses its actual natural projection square.
- The original projection is pointwise coarse-weak, and the first object is
  the original first object, including chains of length zero.
- Pointwise fine-weak natural transformations remain pointwise fine-weak
  after replacement. The proof is induction on the actual recursive stages,
  followed by the existing constant extension and finite restriction.
  Fine two-out-of-three is not assumed.

The projection is only coarse-weak. It is not asserted to be a morphism in
the fine-weak category. These statements alone imply neither a nerve
comparison equivalence nor a fibration theorem. No strict compatibility of
the recursively chosen replacement with arbitrary ordinal restrictions is
claimed. In particular, pointwise fine-map preservation on finite chains
does not prove genuine Reedy row-cofibration or quotient-square preservation
in every inner S-degree. That further obligation requires the accepted
exact joint-cylinder and actual row/arrow lifts, and remains separate.

## Actual complex instance

`Fibration.ComplexChainReplacement` supplies the actual inherited ambient
cofibration factorization on a zero-containing, replete, extension-closed
full complex subcategory with finite-product and actual cone closure.
Its middle functor, inclusion, and projection are literally the accepted
identity-cone construction. Ambient admissibility follows from its proved
split admissibility, including quotient membership in the same category.

`complexSubcategoryNested` uses chain isomorphisms as fine weak maps and
actual quasi-isomorphisms as coarse weak maps. The structural fine-square
condition is proved: isomorphisms at both endpoints make an actual arrow
category isomorphism, and the original middle functor preserves it. No
shift-closure, global projectivity, or kernel-closure input is needed.

The exported actual finite replacement preserves pointwise chain
isomorphisms, resolves quasi-isomorphism chains by inherited admissible
quasi-isomorphisms, and has the original pointwise quasi-isomorphism
projection. Existing bounded-term categories instantiate every object
closure condition. Their nested structure is definitionally the original
`boundedTermsNested` model.

## Verification boundary

Both modules are new. Earlier accepted source files remain unchanged.
`audits/MixedChainReplacementAudit.lean` checks recursive source-origin
axioms and the original cylinder factors, projection naturality, arbitrary
object/hom universes, length-zero chains, bounded-term categories without
kernel closure, and arbitrary-scheme consumers.

Both sources compile warning-free. The final fixed28-origin recursive audit
and all16 consumers passed without warnings, errors, or `sorryAx`, with only
`propext`, `Classical.choice`, and `Quot.sound`. The exact source manifest is
`logs/mixed-chain-replacement-sources.sha256`, the terminal raw audit is
`logs/mixed-chain-replacement-audit.log`, and source rehashes are in
`logs/mixed-chain-replacement-hashes.log`. Independent review passed; see
`docs/REVIEW_20261009_MIXED_CHAIN_REPLACEMENT.md`. Fresh excluded-target
builds, fixed28 origins, all21 strengthened consumers, actual import paths,
and source/dependency hashes passed warning-free.
