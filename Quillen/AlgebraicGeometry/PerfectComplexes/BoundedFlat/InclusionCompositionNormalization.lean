/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.InclusionNormalization
public import Quillen.Aglib.CategoryTheory.Functor.IsoConjugation

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

/-- The two original normalized inclusion/composition routes agree as natural transformations. -/
theorem boundedFlatNormalizedInclusionPullbackIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    whiskerRight (boundedFlatNormalizedPullbackCompIso f g).hom (boundedFlatNormalizedInclusion X) ≫
      whiskerLeft (boundedFlatNormalizedPullback g)
        (boundedFlatNormalizedInclusionPullbackIso f).hom ≫
      whiskerRight (boundedFlatNormalizedInclusionPullbackIso g).hom
        (perfectFlatNormalizedPullback f) =
    (boundedFlatNormalizedInclusionPullbackIso (f ≫ g)).hom ≫
      whiskerLeft (boundedFlatNormalizedInclusion Z)
        (perfectFlatNormalizedPullbackCompIso f g).hom := by
  let s₀₁ : boundedFlatPerfectPullback g ⋙ boundedFlatPerfectInclusion Y ≅
      boundedFlatPerfectInclusion Z ⋙ perfectFlatPullback g := Iso.refl _
  let s₁₂ : boundedFlatPerfectPullback f ⋙ boundedFlatPerfectInclusion X ≅
      boundedFlatPerfectInclusion Y ⋙ perfectFlatPullback f := Iso.refl _
  let s₀₂ : boundedFlatPerfectPullback (f ≫ g) ⋙ boundedFlatPerfectInclusion X ≅
      boundedFlatPerfectInclusion Z ⋙ perfectFlatPullback (f ≫ g) := Iso.refl _
  have he : whiskerRight (boundedFlatPerfectPullbackCompIso f g).hom
        (boundedFlatPerfectInclusion X) ≫
      whiskerLeft (boundedFlatPerfectPullback g) s₁₂.hom ≫
      whiskerRight s₀₁.hom (perfectFlatPullback f) =
      s₀₂.hom ≫ whiskerLeft (boundedFlatPerfectInclusion Z)
        (perfectFlatPullbackCompIso f g).hom := by
    apply NatTrans.ext
    funext K
    have h := congrArg (fun η ↦ η.app K) (boundedFlatPerfectPullbackCompIso_inclusion f g)
    simp only [s₀₁, s₁₂, s₀₂, Iso.refl_hom, NatTrans.comp_app, whiskerLeft_app,
      whiskerRight_app, NatTrans.id_app, map_id, Category.id_comp]
    erw [Category.id_comp, Category.comp_id]
    exact h
  have h := Quillen.FunctorConjugation.squareIso_comp
    (boundedFlatPerfectPullbackCompIso f g) (perfectFlatPullbackCompIso f g) s₀₁ s₁₂ s₀₂
    (boundedFlatPullbackNormalizationIso g) (boundedFlatPullbackNormalizationIso f)
    (boundedFlatPullbackNormalizationIso (f ≫ g))
    (perfectFlatPullbackNormalizationIso g) (perfectFlatPullbackNormalizationIso f)
    (perfectFlatPullbackNormalizationIso (f ≫ g))
    (boundedFlatInclusionNormalizationIso Z) (boundedFlatInclusionNormalizationIso Y)
    (boundedFlatInclusionNormalizationIso X) he
  simpa only [Quillen.FunctorConjugation.compositionIso, Quillen.FunctorConjugation.squareIso,
    s₀₁, s₁₂, s₀₂, Iso.refl_trans, boundedFlatNormalizedPullbackCompIso,
    perfectFlatNormalizedPullbackCompIso, boundedFlatNormalizedInclusionPullbackIso] using h

end Quillen.PerfectComplexes
