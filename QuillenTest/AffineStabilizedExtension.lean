/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StabilizedExtension
public import Mathlib.Data.ZMod.Basic

/-! Original cones, inclusions, shifts and empty-open consumers for stabilized extension. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w v u
namespace QuillenTest.AffineStabilizedExtension

open Quillen

section Algebra
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
attribute [local instance] Abelian.hasFiniteBiproducts

omit [HasDerivedCategory A] in
lemma actual_cone_biprod_inclusion {K₁ L₁ K₂ L₂ : CochainComplex A ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    CochainComplex.mappingCone.inr (biprod.map f g) =
      biprod.map (CochainComplex.mappingCone.inr f) (CochainComplex.mappingCone.inr g) ≫
        (Quillen.CochainComplex.mappingConeBiprodIso f g).inv := by
  rw [← Quillen.CochainComplex.mappingConeBiprodIso_inr, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

lemma zero_cone_original_summand (E : CochainComplex A ℤ) :
    DerivedCategory.Q.map (CochainComplex.mappingCone.inr (0 : E ⟶ E)) ≫
      (Quillen.CochainComplex.zeroConeDerivedIso E).hom =
        DerivedCategory.Q.map (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧) :=
  Quillen.CochainComplex.zeroConeDerivedIso_inr E

lemma original_complement_is_killed (C E : CochainComplex A ℤ) :
    DerivedCategory.Q.map (biprod.inl : C ⟶ C ⊞ E) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr (biprod.map (𝟙 C) (0 : E ⟶ E))) ≫
        (Quillen.CochainComplex.projectorConeDerivedIso C E).hom = 0 := by
  rw [Quillen.CochainComplex.projectorConeDerivedIso_inr, ← DerivedCategory.Q.map_comp]
  simp

lemma original_E_summand_is_retained (C E : CochainComplex A ℤ) :
    DerivedCategory.Q.map (biprod.inr : E ⟶ C ⊞ E) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr (biprod.map (𝟙 C) (0 : E ⟶ E))) ≫
        (Quillen.CochainComplex.projectorConeDerivedIso C E).hom =
          DerivedCategory.Q.map (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧) := by
  rw [Quillen.CochainComplex.projectorConeDerivedIso_inr, ← DerivedCategory.Q.map_comp]
  simp
end Algebra

open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

lemma original_geometric_cone_inclusion (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P) (C E : Complex W.toScheme)
    (e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
      (toDerived W.toScheme).obj (C ⊞ E)) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t g : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      ∃ eCone : (toDerived W.toScheme).obj
        ((restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone g))) ≅
          (toDerived W.toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧),
        (toDerived W.toScheme).map ((restrict W.ι).map
          ((associatedComplex R).map (CochainComplex.mappingCone.inr g))) =
            e.hom ≫ (toDerived W.toScheme).map
              ((biprod.snd : C ⊞ E ⟶ E) ≫ (biprod.inl : E ⟶ E ⊞ E⟦(1 : ℤ)⟧)) ≫ eCone.inv := by
  obtain ⟨P', hP', t, g, ht, _, _, eCone, heCone⟩ :=
    exists_stabilized_extension_cone_of_complement R W hW hP C E e
  refine ⟨P', hP', t, g, ht, eCone, ?_⟩
  rw [← Category.assoc, ← heCone, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma every_original_integer_shift (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) (n : ℤ) :
    ∃ (Q : Complex (Spec R)), strictPerfect (Spec R) Q ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj Q) ≅
        (toDerived W.toScheme).obj (E⟦n⟧ ⊞ (E⟦n⟧)⟦(1 : ℤ)⟧)) :=
  locallyPerfect_exists_global_strict_stabilized_extension R W hW (E⟦n⟧) (locallyPerfect_shift hE n)

lemma empty_zero_ring_original_extension
    (E : Complex (⊥ : (Spec (CommRingCat.of (ZMod 1))).Opens).toScheme)
    (hE : locallyPerfect (⊥ : (Spec (CommRingCat.of (ZMod 1))).Opens).toScheme E) :
    ∃ (P P' : ModuleComplex (CommRingCat.of (ZMod 1)))
      (_ : moduleStrictPerfect (CommRingCat.of (ZMod 1)) P)
      (_ : moduleStrictPerfect (CommRingCat.of (ZMod 1)) P') (g : P' ⟶ P),
      moduleStrictPerfect (CommRingCat.of (ZMod 1)) (CochainComplex.mappingCone g) ∧
      Nonempty ((toDerived (⊥ : (Spec (CommRingCat.of (ZMod 1))).Opens).toScheme).obj
        ((restrict (⊥ : (Spec (CommRingCat.of (ZMod 1))).Opens).ι).obj
          ((associatedComplex (CommRingCat.of (ZMod 1))).obj (CochainComplex.mappingCone g))) ≅
        (toDerived (⊥ : (Spec (CommRingCat.of (ZMod 1))).Opens).toScheme).obj (E ⊞ E⟦(1 : ℤ)⟧)) :=
  locallyPerfect_exists_stabilized_extension_cone (CommRingCat.of (ZMod 1)) ⊥ (by simp) E hE

end QuillenTest.AffineStabilizedExtension
