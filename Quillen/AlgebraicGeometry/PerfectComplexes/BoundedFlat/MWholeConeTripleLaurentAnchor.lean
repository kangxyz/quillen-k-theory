/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackSimplex

/-!
# The normalized triple Laurent reference retains the frozen source-whiskered anchor

The canonical total-to-projection normalization anchors the actual triple input. The original
right-first coefficient comparison, followed by the inverse middle-product normalization of
the old binary cube, recovers the literal frozen precomposition anchor. This is an equality
of full natural isomorphisms before realization or native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.TripleLaurent
open BassH0Merge BassReferenceMerge
attribute [local irreducible] boundedFlatNormalizedPullback

variable {R : CommRingCat.{u}} (P : Over (Spec R))

private theorem binary_reference_middle {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c) :
    BassMWholeConeCarrier.referenceIso P p q = (BassMReferences.middleIso P p q).symm := by
  unfold BassMWholeConeCarrier.referenceIso
    CoefficientBassSeedCarrierLaurentReference.referenceIso BassMReferences.middleIso
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

variable {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d)
local notation "f" => coefficientMap P r
local notation "g" => coefficientMap P q
local notation "h" => coefficientMap P p
local notation "t" => laurentPlus P d ≫ polynomialProjection P d

/-- The unchanged normalized source of the coefficient triple. -/
abbrev input := NormalizedTripleSimplex.sourceMap f g h

/-- The literal input obtained by source-precomposing the binary carrier for `q, r`. -/
abbrev precompInput := normalizedMap h ≫ BinaryNormalizationSimplex.sourceMap f g

/-- Only the presentation by small-model functors changes. -/
theorem precompInput_functor : (precompInput P p q r).functor =
    (NormalizedTripleSimplex.rightMap f g h).functor := rfl

/-- The actual right-first edge retains its scheme association transport. -/
def inputIso : (input P p q r).functor ≅ (precompInput P p q r).functor :=
  NormalizedTripleSimplex.rightFirst f g h ≪≫
    eqToIso (precompInput_functor P p q r).symm

/-- The shallow presentation equality adds no new comparison to the original edge. -/
theorem inputIso_small : inputIso P p q r =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (f ≫ g) h) := by
  change NormalizedTripleSimplex.rightFirst f g h ≪≫ Iso.refl _ = _
  rw [Iso.trans_refl]
  rfl

/-- The total equation uses the actual positive projection source and triple association. -/
theorem total :
    coefficientMap P ((laurentUnderFunctor R).map ((p ≫ q) ≫ r)) ≫
      laurentProjection P a = t ≫ (f ≫ g ≫ h) := by
  rw [BassMWholeNerve.precomp_total P p q r, laurentPlus_projection P d]
  simp only [Category.assoc]

/-- Canonical normalization from the frozen H0 total into the whole triple Laurent reference. -/
def anchor : (BassH0Diagram.reference P ((p ≫ q) ≫ r)).functor ≅
    (BassProjectionPath.WholeReference.reference P d (input P p q r)).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (total P p q r)) ≪≫
    boundedFlatNormalizedPullbackCompIso t (f ≫ g ≫ h))

/-- The full anchor equality before composing with the old binary Laurent reference. -/
theorem anchor_right :
    anchor P p q r ≪≫ isoWhiskerRight (inputIso P p q r)
        (BassProjectionPath.source P d).functor =
      BassMWholeNerve.precompAnchor P p q r ≪≫
        isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor
          (BassMWholeConeCarrier.referenceIso P q r).symm := by
  rw [inputIso_small, binary_reference_middle, Iso.symm_symm_eq]
  change
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (total P p q r)) ≪≫
      boundedFlatNormalizedPullbackCompIso t (f ≫ g ≫ h)) ≪≫
        isoWhiskerRight
          (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
              (Category.assoc f g h).symm) ≪≫
            boundedFlatNormalizedPullbackCompIso (f ≫ g) h))
          (AsSmall.down ⋙ boundedFlatNormalizedPullback t ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (BassMWholeNerve.precomp_total P p q r)) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurentProjection P d ≫ f ≫ g) h) ≪≫
        isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback h ⋙ AsSmall.up)
          (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
              (BassMReferences.middle_total P q r).symm) ≪≫
            boundedFlatNormalizedPullbackCompIso t (f ≫ g)))
  rw [smallIso_postcomp, smallIso_precomp]
  have hraw := (anchored_factorizations_strict t (f ≫ g) h
    (laurentProjection P d ≫ f ≫ g) (f ≫ g ≫ h) _
    (BassMReferences.middle_total P q r).symm (Category.assoc f g h).symm
    (BassMWholeNerve.precomp_total P p q r) (total P p q r)).symm
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso hraw

/-- The transported binary carrier has exactly the frozen original precomposition anchor. -/
theorem anchor_join :
    (anchor P p q r ≪≫ isoWhiskerRight (inputIso P p q r)
        (BassProjectionPath.source P d).functor) ≪≫
      isoWhiskerLeft (BassMWholeNerve.coefficientModel P p).functor
        (BassMWholeConeCarrier.referenceIso P q r) =
      BassMWholeNerve.precompAnchor P p q r := by
  rw [anchor_right]
  simp only [Iso.trans_assoc, ← isoWhiskerLeft_trans, Iso.symm_self_id,
    isoWhiskerLeft_refl]
  apply Iso.ext
  ext X
  simp only [Iso.trans_hom, Iso.refl_hom, NatTrans.comp_app, NatTrans.id_app]
  exact Category.comp_id ((BassMWholeNerve.precompAnchor P p q r).hom.app X)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.TripleLaurent
