/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.Derived
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Semantic original-derived-overlap consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v w
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.DerivedOpenPerfectGluing
section Denominator
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- One original source denominator realizes both equalities by actual homotopies. -/
theorem simultaneous_original_homotopies {K L₁ L₂ : CochainComplex C ℤ}
    (f₁ g₁ : K ⟶ L₁) (f₂ g₂ : K ⟶ L₂)
    (h₁ : DerivedCategory.Q.map f₁ = DerivedCategory.Q.map g₁)
    (h₂ : DerivedCategory.Q.map f₂ = DerivedCategory.Q.map g₂) :
    ∃ (M : CochainComplex C ℤ) (s : M ⟶ K), QuasiIso s ∧
      Nonempty (Homotopy (s ≫ f₁) (s ≫ g₁)) ∧ Nonempty (Homotopy (s ≫ f₂) (s ≫ g₂)) :=
  Quillen.CochainComplex.exists_pre_quasiIso_two_homotopies_of_derived_eq f₁ g₁ f₂ g₂ h₁ h₂

/-- The actual weak span reconstructs the specified original isomorphism as its true right fraction.
  -/
theorem original_iso_as_actual_fraction {A B T : CochainComplex C ℤ}
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B) (p : A ⟶ T) (q : B ⟶ T)
    (he : DerivedCategory.Q.map p = e.hom ≫ DerivedCategory.Q.map q) :
    ∃ (K : CochainComplex C ℤ) (a : K ⟶ A) (b : K ⟶ B),
      QuasiIso a ∧ QuasiIso b ∧ Nonempty (Homotopy (a ≫ p) (b ≫ q)) ∧
      ∃ ea : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj A,
        ea.hom = DerivedCategory.Q.map a ∧ e.hom = ea.inv ≫ DerivedCategory.Q.map b := by
  obtain ⟨K, a, b, ha, hb, hfac, H⟩ :=
    Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso e p q he
  refine ⟨K, a, b, ha, hb, H, asIso (DerivedCategory.Q.map a), rfl, ?_⟩
  change e.hom = inv (DerivedCategory.Q.map a) ≫ DerivedCategory.Q.map b
  rw [← hfac, IsIso.inv_hom_id_assoc]
end Denominator

open Quillen.PerfectComplexes.OpenHomotopyGluing
section Geometric
variable {X : Scheme.{u}} (U V : X.Opens)
  {A : CochainComplex U.toScheme.Modules ℤ} {B : CochainComplex V.toScheme.Modules ℤ}
    {L : CochainComplex X.Modules ℤ}
  (hUV : U ⊔ V = ⊤) (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
  (e : (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
    ((restrict (pullback.fst U.ι V.ι)).obj A) ≅
    (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
      ((restrict (pullback.snd U.ι V.ι)).obj B))

include hUV hA hB in
/-- The gluing realizes the entire original derived transition, recovered from its actual
  comparisons. -/
theorem original_transition_recovered :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (a : A ⟶ (restrict U.ι).obj P) (b : B ⟶ (restrict V.ι).obj P),
        QuasiIso a ∧ QuasiIso b ∧
        ∃ eb : (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
          ((restrict (pullback.snd U.ι V.ι)).obj B) ≅
            (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
              ((restrict (pullback.fst U.ι V.ι)).obj ((restrict
              U.ι).obj P)),
          eb.hom = (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
            ((restrict (pullback.snd U.ι V.ι)).map b ≫
              (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
                V.ι U.ι pullback.condition.symm).hom.app P) ∧
          e.hom = (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
            ((restrict (pullback.fst U.ι V.ι)).map a) ≫
            eb.inv := by
  obtain ⟨P, hP, a, b, ha, hb, he⟩ := exists_perfect_glue_of_derived_iso U V hUV hA hB e
  let c := (restrict (pullback.snd U.ι V.ι)).map b ≫
    (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
      V.ι U.ι pullback.condition.symm).hom.app P
  have : QuasiIso c := by dsimp [c]; infer_instance
  refine ⟨P, hP, a, b, ha, hb, asIso ((DerivedCategory.Q
    (C := (pullback U.ι V.ι).Modules)).map c), rfl, ?_⟩
  change e.hom = (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
    ((restrict (pullback.fst U.ι V.ι)).map a) ≫
    inv ((DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map c)
  change _ = e.hom ≫ (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map c at he
  rw [he, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

include hUV hA hB in
/-- Arbitrary target maps remain the original strict triangles after deriving overlap data. -/
theorem original_target_equations
    (p : A ⟶ (restrict U.ι).obj L) (q : B ⟶ (restrict V.ι).obj L)
    (he : (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
      ((restrict (pullback.fst U.ι V.ι)).map p) =
      e.hom ≫ (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).map
        ((restrict (pullback.snd U.ι V.ι)).map q ≫
          (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
            V.ι U.ι pullback.condition.symm).hom.app L)) :
    ∃ (P : CochainComplex X.Modules ℤ) (_ : locallyPerfect X P)
      (a : A ⟶ (restrict U.ι).obj P) (b : B ⟶ (restrict V.ι).obj P) (d : P ⟶ L),
      QuasiIso a ∧ QuasiIso b ∧ a ≫ (restrict U.ι).map d = p ∧ b ≫ (restrict V.ι).map d = q := by
  obtain ⟨P, hP, a, b, d, ha, hb, hp, hq, _⟩ :=
    exists_perfect_glue_of_derived_overlap U V hUV hA hB e p q he
  exact ⟨P, hP, a, b, d, ha, hb, hp, hq⟩
end Geometric
end QuillenTest.DerivedOpenPerfectGluing
