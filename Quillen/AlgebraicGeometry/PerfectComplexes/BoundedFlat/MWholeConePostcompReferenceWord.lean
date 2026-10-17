/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceCoherence

/-! Two original normalization triangles give the full target-projection reference word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.BassReferenceMerge

private theorem cancel_whiskered_triangles
    {V Z B X : Type*} [Category V] [Category Z] [Category B] [Category X]
    (J : V ⥤ Z) (Q : Z ⥤ B) (L : B ⥤ X)
    {F : V ⥤ X} {A D : Z ⥤ X} {R : V ⥤ B}
    (t : A ≅ D) (s : A ≅ Q ⋙ L) (c : R ≅ J ⋙ Q)
    (a : F ≅ J ⋙ A) (b : F ≅ J ⋙ D) (d : F ≅ R ⋙ L)
    (hfirst : a ≪≫ isoWhiskerLeft J t = b)
    (hsecond : a ≪≫ isoWhiskerLeft J s = d ≪≫ isoWhiskerRight c L) :
    b ≪≫ isoWhiskerLeft J (t.symm ≪≫ s) ≪≫ isoWhiskerRight c.symm L = d := by
  rw [← hfirst]
  simp only [isoWhiskerLeft_trans, ← isoWhiskerLeft_symm, Iso.trans_assoc,
    Iso.self_symm_id_assoc]
  have hc := congrArg (fun e ↦ e ≪≫ isoWhiskerRight c.symm L) hsecond
  simpa only [← isoWhiskerRight_symm, Iso.trans_assoc, Iso.self_symm_id,
    Iso.trans_refl] using hc

/-- The original left-first route, target projection square and old reference inverse agree. -/
theorem postcomp_projection_word {X Y Z T B : Scheme.{u}}
    (t : X ⟶ Y) (k : Y ⟶ Z) (j : Z ⟶ T) (l : X ⟶ B) (s : B ⟶ Z)
    (r : B ⟶ T) (w : X ⟶ T)
    (hd : t ≫ k = l ≫ s) (he : r = s ≫ j)
    (hl : w = (t ≫ k) ≫ j) (hr : w = t ≫ k ≫ j) (hp : w = l ≫ r) :
    ((eqToIso (congrArg boundedFlatNormalizedPullback hr) ≪≫
        boundedFlatNormalizedPullbackCompIso t (k ≫ j)) ≪≫
      isoWhiskerRight (boundedFlatNormalizedPullbackCompIso k j)
        (boundedFlatNormalizedPullback t)) ≪≫
      isoWhiskerLeft (boundedFlatNormalizedPullback j)
        ((boundedFlatNormalizedPullbackCompIso t k).symm ≪≫
          eqToIso (congrArg boundedFlatNormalizedPullback hd) ≪≫
            boundedFlatNormalizedPullbackCompIso l s) ≪≫
      isoWhiskerRight
        (eqToIso (congrArg boundedFlatNormalizedPullback he) ≪≫
          boundedFlatNormalizedPullbackCompIso s j).symm
        (boundedFlatNormalizedPullback l) =
    eqToIso (congrArg boundedFlatNormalizedPullback hp) ≪≫
      boundedFlatNormalizedPullbackCompIso l r := by
  apply cancel_whiskered_triangles
    (boundedFlatNormalizedPullback j) (boundedFlatNormalizedPullback s)
    (boundedFlatNormalizedPullback l) (boundedFlatNormalizedPullbackCompIso t k)
    (eqToIso (congrArg boundedFlatNormalizedPullback hd) ≪≫
      boundedFlatNormalizedPullbackCompIso l s)
    (eqToIso (congrArg boundedFlatNormalizedPullback he) ≪≫
      boundedFlatNormalizedPullbackCompIso s j)
    (eqToIso (congrArg boundedFlatNormalizedPullback hl) ≪≫
      boundedFlatNormalizedPullbackCompIso (t ≫ k) j)
  · simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
      anchored_factorizations_strict t k j (t ≫ k) (k ≫ j) w rfl rfl hl hr
  · simpa only [Iso.trans_assoc] using
      anchored_factorizations_strict l s j (t ≫ k) r w hd he hl hp

end Quillen.PerfectComplexes.BassReferenceMerge
