/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.OpenWeakImage

/-! # Actual weak-image and original relative-open comparison consumers -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v u' v'
namespace Quillen.Tests.ApproximationWeakImage
open Waldhausen
open ApproximationImage
section Categorical
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationOnImage W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF in
/-- The original target zero has an actual source representative without a chosen point. -/
theorem target_zero_has_original_comparison :
    ∃ (A : C) (p : F.obj A ⟶ V.zero), V.weq p := zero_mem hF

include h hF in
/-- Closure yields a weak comparison into the actual specified ambient pushout. -/
theorem actual_ambient_pushout_has_comparison
    {A B E Q : D} {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ Q} {j : E ⟶ Q}
    (hi : V.cof i) (hQ : IsPushout i f g j)
    (hA : objects V F A) (hB : objects V F B) (hE : objects V F E) :
    ∃ (T : C) (p : F.obj T ⟶ Q), V.weq p := pushout_mem h hF hi hQ hA hB hE

include h hF in
/-- An arbitrary already-chosen image-category pushout remains the ambient pushout. -/
theorem actual_inclusion_preserves_pushout
    {A B E Q : Obj V F} {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ Q} {j : E ⟶ Q}
    (hi : V.cof i.hom) (hQ : IsPushout i f g j) :
    IsPushout i.hom f.hom g.hom j.hom :=
  (inclusion_exact h hF).pushout hi hQ

include h in
/-- Only the target witness is needed to factor an arbitrary actual target arrow. -/
theorem actual_relative_arrow_factorization {A E : C} {B : D}
    (q : F.obj E ⟶ B) (hq : V.weq q) (f : F.obj A ⟶ B) :
    ∃ (A' : C) (a : A ⟶ A') (p : F.obj A' ⟶ B),
      W.cof a ∧ V.weq p ∧ F.map a ≫ p = f := h.lift f ⟨E, q, hq⟩

/-- Forgetting the corestriction leaves every original composite exactly unchanged. -/
theorem literal_corestriction_composite {A B E : C} (a : A ⟶ B) (b : B ⟶ E) :
    ((objects V F).ι.map ((corestrict V F).map a ≫ (corestrict V F).map b)) =
      F.map (a ≫ b) := (F.map_comp a b).symm

/-- The inherited weak and cofibration classes are exactly the original target classes. -/
theorem literal_map_classes {A B : Obj V F} (f : A ⟶ B) :
    ((waldhausenStructure h hF).cof f ↔ V.cof f.hom) ∧
      ((waldhausenStructure h hF).weq f ↔ V.weq f.hom) := ⟨Iff.rfl, Iff.rfl⟩
end Categorical

section KTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationOnImage W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

/-- Pulling an image class back and then applying the original map gives its actual inclusion. -/
theorem inverse_class_original_map (n : ℕ) (a : (waldhausenStructure h hF).K n) :
    KMap hF n ((corestrictKEquiv h hF J n).symm a) = KMap (inclusion_exact h hF) n a := by
  rw [← DFunLike.congr_fun (inclusion_KMap_comp_corestrict h hF n)
    ((corestrictKEquiv h hF J n).symm a), MonoidHom.comp_apply]
  exact congrArg (KMap (inclusion_exact h hF) n) ((corestrictKEquiv h hF J n).apply_symm_apply a)

include J in
/-- The missing inclusion injectivity condition is exactly original K-map injectivity. -/
theorem inclusion_injective_iff_original (n : ℕ) :
    Function.Injective (KMap (inclusion_exact h hF) n) ↔ Function.Injective (KMap hF n) := by
  constructor
  · intro hi a b hab
    apply (corestrict_KMap_bijective h hF J n).injective
    apply hi
    simpa only [← MonoidHom.comp_apply, inclusion_KMap_comp_corestrict] using hab
  · intro hf a b hab
    obtain ⟨a', rfl⟩ := (corestrict_KMap_bijective h hF J n).surjective a
    obtain ⟨b', rfl⟩ := (corestrict_KMap_bijective h hF J n).surjective b
    exact congrArg (KMap (corestrict_exact h hF) n)
      (hf (by simpa only [← MonoidHom.comp_apply, inclusion_KMap_comp_corestrict] using hab))
end KTheory
end Quillen.Tests.ApproximationWeakImage

namespace Quillen.Tests.PerfectOpenWeakImage
open PerfectComplexes Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (h : OpenWeakImage.HasMapFactorization j)

include h in
/-- The sole geometric input gives a source cofibration and literal original factorization. -/
theorem actual_geometric_factorization {A E : Perfect X} {B : Perfect U}
    (q : (perfectRestrict j).obj E ⟶ B) (hq : (perfectWaldhausen U).weq q)
    (f : (perfectRestrict j).obj A ⟶ B) :
    ∃ (A' : Perfect X) (a : A ⟶ A') (p : (perfectRestrict j).obj A' ⟶ B),
      (perfectOpenWeakWaldhausen j).cof a ∧ (perfectWaldhausen U).weq p ∧
        (perfectRestrict j).map a ≫ p = f :=
  (OpenWeakImage.approximationOnImage h).lift f ⟨E, q, hq⟩

/-- The original relative class obtained from an image class has the original restriction value. -/
theorem original_restriction_of_inverse (n : ℕ) (a : (OpenWeakImage.waldhausenStructure h).K n) :
    perfectOpenKRestrict j n ((OpenWeakImage.KEquiv h n).symm a) =
      KMap (OpenWeakImage.inclusion_exact h) n a := by
  rw [← DFunLike.congr_fun (OpenWeakImage.inclusion_KMap_comp h n)
    ((OpenWeakImage.KEquiv h n).symm a), MonoidHom.comp_apply]
  exact congrArg (KMap (OpenWeakImage.inclusion_exact h) n)
    ((OpenWeakImage.KEquiv h n).apply_symm_apply a)

/-- Every image-category K-zero class has a representative under original restriction from X. -/
theorem image_class_has_original_X_representative
    (a : (OpenWeakImage.waldhausenStructure h).K 0) :
    ∃ b : PerfectK X 0, perfectKRestrict j 0 b = KMap (OpenWeakImage.inclusion_exact h) 0 a := by
  change KMap (OpenWeakImage.inclusion_exact h) 0 a ∈ (perfectKRestrict j 0).range
  rw [← OpenWeakImage.range_inclusion_KMap_zero h]
  exact ⟨a, rfl⟩

/-- The image inclusion is not asserted surjective when original K-zero restriction is not. -/
theorem inclusion_not_surjective_of_original_not_surjective
    (hn : ¬ Function.Surjective (perfectKRestrict j 0)) :
    ¬ Function.Surjective (KMap (OpenWeakImage.inclusion_exact h) 0) := by
  intro hs
  apply hn
  intro y
  obtain ⟨a, rfl⟩ := hs y
  exact image_class_has_original_X_representative j h a

end Quillen.Tests.PerfectOpenWeakImage
