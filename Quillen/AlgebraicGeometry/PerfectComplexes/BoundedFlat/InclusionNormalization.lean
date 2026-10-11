/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.NormalizedFlatPullback

/-!
# Original normalized bounded-flat inclusion and geometric composition

The literal inclusion commutes with the two actual geometric pullback composition isomorphisms.
After the original chosen-zero normalizations, the resulting inclusion squares retain that full
categorical compatibility. These are equalities of actual natural transformations before their
whole prespectrum tracks are realized.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual chosen-zero normalization of the bounded-flat inclusion. -/
def boundedFlatNormalizedInclusion (X : Scheme.{u}) : BoundedFlatPerfect X ⥤ Perfect X :=
  Quillen.rebaseFunctor (boundedFlatPerfectInclusion X)
    (boundedFlatPerfectWaldhausen X).zero (perfectWaldhausen X).zero
    (((boundedFlatPerfectInclusion_exact X).zero (boundedFlatPerfectWaldhausen X).isZero).iso
      (perfectWaldhausen X).isZero)

/-- The unchanged canonical normalization isomorphism of the original inclusion. -/
def boundedFlatInclusionNormalizationIso (X : Scheme.{u}) :
    boundedFlatPerfectInclusion X ≅ boundedFlatNormalizedInclusion X :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The actual inclusion square between the original normalized flat-pullback functors. -/
def boundedFlatNormalizedInclusionPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    boundedFlatNormalizedPullback f ⋙ boundedFlatNormalizedInclusion X ≅
      boundedFlatNormalizedInclusion Y ⋙ perfectFlatNormalizedPullback f :=
  (isoWhiskerLeft (boundedFlatNormalizedPullback f)
    (boundedFlatInclusionNormalizationIso X)).symm ≪≫
    (isoWhiskerRight (boundedFlatPullbackNormalizationIso f)
      (boundedFlatPerfectInclusion X)).symm ≪≫
    isoWhiskerRight (boundedFlatInclusionNormalizationIso Y) (perfectFlatPullback f) ≪≫
    isoWhiskerLeft _ (perfectFlatPullbackNormalizationIso f)

/-- The literal inclusion preserves the original geometric composition transformation. -/
theorem boundedFlatPerfectPullbackCompIso_inclusion {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    whiskerRight (boundedFlatPerfectPullbackCompIso f g).hom (boundedFlatPerfectInclusion X) =
      whiskerLeft (boundedFlatPerfectInclusion Z) (perfectFlatPullbackCompIso f g).hom := by
  apply NatTrans.ext
  funext K
  apply (locallyPerfect X).ι.map_injective
  simp only [whiskerRight_app, whiskerLeft_app, boundedFlatPerfectPullbackCompIso,
    perfectFlatPullbackCompIso, fullyFaithfulCancelRight_hom_app, isoWhiskerLeft_hom,
    map_preimage]
  change (boundedFlatPerfect X).ι.map ((boundedFlatPerfect X).ι.preimage _) = _
  rw [map_preimage]
  rfl

end Quillen.PerfectComplexes
