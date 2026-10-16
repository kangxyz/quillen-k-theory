/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ApproximationTriangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedDenominators
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ScalarNilpotence
public import Mathlib.CategoryTheory.Retract
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-! # Actual finite scalar cones force source support

The genuine scalar-nilpotence theorem supplies every exponent. The original
cone inclusions preserve a displayed local retract; the actual finite
iteration keeps its original composite chain map and all earlier open and
principal acyclicity conditions. No scalar exponent or support extension
is supplied to the finite-family endpoint.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- If the original restricted arrow is zero in the derived category, the
original cone inclusion has a genuine derived retraction. -/
lemma exists_retraction_original_cone_inclusion_of_restrict_zero
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P B : ModuleComplex R} (f : P ⟶ B)
    (hf : (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map ((associatedComplex R).map f))
      = 0) :
    ∃ ρ : (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone
      f))) ⟶
        (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj ((associatedComplex R).obj B)),
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map
        ((associatedComplex R).map (CochainComplex.mappingCone.inr f))) ≫ ρ = 𝟙 _ := by
  let g := (restrict j).map ((associatedComplex R).map f)
  obtain ⟨ρ, hρ⟩ := Triangle.yoneda_exact₂ _
    (DerivedCategory.mappingCone_triangle_distinguished g) (𝟙 _) (by
      change (DerivedCategory.Q (C := U.Modules)).map g ≫ 𝟙 _ = 0
      rw [Category.comp_id]
      exact hf)
  change (DerivedCategory.Q (C := U.Modules)).obj (CochainComplex.mappingCone g) ⟶
    (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj ((associatedComplex R).obj B)) at ρ
  change 𝟙 _ = (DerivedCategory.Q (C := U.Modules)).map (CochainComplex.mappingCone.inr g) ≫ ρ at hρ
  refine ⟨(DerivedCategory.Q (C := U.Modules)).map (openAssociatedConeIso R j f).hom ≫ ρ, ?_⟩
  rw [← Category.assoc, ← (DerivedCategory.Q (C := U.Modules)).map_comp, openAssociatedConeIso_inr]
  exact hρ.symm

/-- Successive scalar cones can retain the same original local derived
summand, using the original restricted cone-inclusion as transition. -/
lemma exists_retract_into_scalar_cone
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P : ModuleComplex R} {E : CochainComplex U.Modules ℤ}
    (r : Retract ((DerivedCategory.Q (C := U.Modules)).obj E)
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj ((associatedComplex R).obj P))))
    (s : R) (n : ℕ)
    (hs : (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map
      ((associatedComplex R).map (s ^ n • 𝟙 P))) = 0) :
    ∃ r' : Retract ((DerivedCategory.Q (C := U.Modules)).obj E)
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj
        ((associatedComplex R).obj (CochainComplex.mappingCone (s ^ n • 𝟙 P))))),
      r'.i = r.i ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map
        ((associatedComplex R).map (CochainComplex.mappingCone.inr (s ^ n • 𝟙 P)))) := by
  obtain ⟨ρ, hρ⟩ := exists_retraction_original_cone_inclusion_of_restrict_zero R j (s ^ n • 𝟙 P) hs
  exact ⟨r.trans {
    i := (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map
      ((associatedComplex R).map (CochainComplex.mappingCone.inr (s ^ n • 𝟙 P))))
    r := ρ
    retract := hρ }, rfl⟩

/-- A genuine scalar-nullhomotopy step adds the selected principal support,
keeps every prior source support, and preserves the original local summand. -/
lemma scalar_cone_adds_support_and_preserves_retract
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P) {E : CochainComplex U.Modules ℤ}
    (r : Retract ((DerivedCategory.Q (C := U.Modules)).obj E)
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj ((associatedComplex R).obj P))))
    (s : R) (n : ℕ)
    (hs : (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map
      ((associatedComplex R).map (s ^ n • 𝟙 P))) = 0) :
    moduleStrictPerfect R (CochainComplex.mappingCone (s ^ n • 𝟙 P)) ∧
    IsZero (DerivedCategory.Q.obj ((localize s (.up ℤ)).obj
      (CochainComplex.mappingCone (s ^ n • 𝟙 P)))) ∧
    (∀ z : R, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj P)) →
      IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj
        (CochainComplex.mappingCone (s ^ n • 𝟙 P))))) ∧
    ∃ r' : Retract ((DerivedCategory.Q (C := U.Modules)).obj E)
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj
        ((associatedComplex R).obj (CochainComplex.mappingCone (s ^ n • 𝟙 P))))),
      r'.i = r.i ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map
        ((associatedComplex R).map (CochainComplex.mappingCone.inr (s ^ n • 𝟙 P)))) := by
  have hi : IsIso ((localize s (.up ℤ)).map (s ^ n • 𝟙 P)) :=
    localize_power_id_isIso s P n
  exact ⟨moduleStrictPerfect_mappingCone R hP hP _,
    isZero_localized_mappingCone_of_isIso R s _,
    (fun z hz => isZero_localized_mappingCone_of_isZero R z _ hz hz),
    exists_retract_into_scalar_cone R j r s n hs⟩

/-- The actual associated/restricted cone preserves acyclicity on every
additional open, independently of the selected scalar support condition. -/
lemma isZero_restrict_associated_mappingCone_of_isZero
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P B : ModuleComplex R} (f : P ⟶ B)
    (hP : IsZero ((DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj ((associatedComplex R).obj P))))
    (hB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj ((associatedComplex R).obj B)))) :
    IsZero ((DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f)))) := by
  exact (Triangle.isZero₃_of_isZero₁₂ _
    (DerivedCategory.mappingCone_triangle_distinguished
      ((restrict j).map ((associatedComplex R).map f))) hP hB).of_iso
        ((DerivedCategory.Q (C := U.Modules)).mapIso (openAssociatedConeIso R j f))

/-- Actual successive scalar cones force a finite principal support condition.
The original summand inclusion is transported along one actual global chain
map. Every earlier open and principal source-acyclicity condition is retained. -/
lemma exists_finite_scalar_cone_support (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (s : Finset R) {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    {E : CochainComplex W.toScheme.Modules ℤ}
    (r : Retract ((DerivedCategory.Q (C := W.toScheme.Modules)).obj E)
      ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
        ((restrict W.ι).obj ((associatedComplex R).obj P))))
    (hlocal : ∀ z ∈ s, IsZero ((DerivedCategory.Q (C :=
      (W ⊓ PrimeSpectrum.basicOpen z).toScheme.Modules)).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen z).ι).obj ((associatedComplex R).obj P)))) :
    ∃ (Q : ModuleComplex R) (_ : moduleStrictPerfect R Q) (i : P ⟶ Q)
      (rQ : Retract ((DerivedCategory.Q (C := W.toScheme.Modules)).obj E)
        ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
          ((restrict W.ι).obj ((associatedComplex R).obj Q)))),
      rQ.i = r.i ≫ (DerivedCategory.Q (C := W.toScheme.Modules)).map
        ((restrict W.ι).map ((associatedComplex R).map i)) ∧
      (∀ z ∈ s, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q))) ∧
      (∀ Z : (Spec R).Opens,
        IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj
          ((restrict Z.ι).obj ((associatedComplex R).obj P))) →
        IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj
          ((restrict Z.ι).obj ((associatedComplex R).obj Q)))) ∧
      ∀ z : R, IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize z (.up ℤ)).obj Q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨P, hP, 𝟙 _, r, by simp only [CategoryTheory.Functor.map_id, Category.comp_id],
      by simp, fun _ h => h, fun _ h => h⟩
  | @insert z s hz ih =>
    obtain ⟨Q, hQ, i, rQ, hi, hQS, hQO, hQP⟩ :=
      ih (fun t ht => hlocal t (Finset.mem_insert_of_mem ht))
    obtain ⟨n, hn⟩ := exists_scalar_power_zero_of_isZero_on_intersection R W hW z hQ
      (hQO _ (hlocal z (Finset.mem_insert_self _ _)))
    let d : Q ⟶ Q := z ^ n • 𝟙 Q
    obtain ⟨hM, hzM, hMP, rM, hrM⟩ :=
      scalar_cone_adds_support_and_preserves_retract R W.ι hQ rQ z n hn
    refine ⟨CochainComplex.mappingCone d, hM, i ≫ CochainComplex.mappingCone.inr d,
      rM, ?_, ?_, ?_, ?_⟩
    · rw [hrM, hi, (associatedComplex R).map_comp, (restrict W.ι).map_comp,
        (DerivedCategory.Q (C := W.toScheme.Modules)).map_comp, Category.assoc]
    · intro t ht
      rcases Finset.mem_insert.mp ht with htz | ht
      · subst t; exact hzM
      · exact hMP t (hQS t ht)
    · intro Z hZ
      exact isZero_restrict_associated_mappingCone_of_isZero R Z.ι d (hQO Z hZ) (hQO Z hZ)
    · intro t ht
      exact hMP t (hQP t ht)

end Quillen.PerfectComplexes.Affine
