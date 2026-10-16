/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Roofs
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-! # Actual global model transport for the open-derived roof interface -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Two specified global derived arrows have one genuine globally weak source
denominator and original chain numerators with exact localization equations. -/
theorem common_global_right_fraction {P A B : CochainComplex X.Modules ℤ}
    (α : (DerivedCategory.Q (C := X.Modules)).obj P ⟶ (DerivedCategory.Q (C := X.Modules)).obj A)
    (β : (DerivedCategory.Q (C := X.Modules)).obj P ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (M : CochainComplex X.Modules ℤ) (s : M ⟶ P) (a : M ⟶ A) (b : M ⟶ B),
      QuasiIso s ∧ (DerivedCategory.Q (C := X.Modules)).map s ≫ α =
        (DerivedCategory.Q (C := X.Modules)).map a ∧
      (DerivedCategory.Q (C := X.Modules)).map s ≫ β =
        (DerivedCategory.Q (C := X.Modules)).map b := by
  obtain ⟨M₁, s₁, hDenIso2, a₁, hFac2⟩ := DerivedCategory.right_fac α
  have hs₁ : QuasiIso s₁ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s₁).1 hDenIso2
  have ha : DerivedCategory.Q.map s₁ ≫ (α) = DerivedCategory.Q.map a₁ := by
    let := hDenIso2
    rw [hFac2, IsIso.hom_inv_id_assoc]
  obtain ⟨M₂, s₂, hDenIso1, b, hFac1⟩ := DerivedCategory.right_fac ((DerivedCategory.Q (C :=
    X.Modules)).map s₁ ≫ β)
  have hs₂ : QuasiIso s₂ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s₂).1 hDenIso1
  have hb : DerivedCategory.Q.map s₂ ≫ (((DerivedCategory.Q (C := X.Modules)).map s₁ ≫ β)) =
    DerivedCategory.Q.map b := by
    let := hDenIso1
    rw [hFac1, IsIso.hom_inv_id_assoc]
  refine ⟨M₂, s₂ ≫ s₁, s₂ ≫ a₁, b, inferInstance, ?_, ?_⟩
  · simp only [Functor.map_comp, Category.assoc, ha]
  · simpa only [Functor.map_comp, Category.assoc] using hb

/-- Actual open roofs on globally chosen models imply the full roof interface.
The final two numerators are obtained by a GLOBAL weak right denominator;
no all-sheaf supported-denominator assertion is used. -/
theorem hasDerivedRoofs_of_models
    (Q : ObjectProperty (CochainComplex X.Modules ℤ))
    (hmodels : ∀ (P : CochainComplex X.Modules ℤ), locallyPerfect X P →
      ∃ A : CochainComplex X.Modules ℤ, Q A ∧ Nonempty
        ((DerivedCategory.Q (C := X.Modules)).obj A ≅ (DerivedCategory.Q (C := X.Modules)).obj P))
    (hroof : ∀ (A P : CochainComplex X.Modules ℤ), Q A → Q P →
      ∀ α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ⟶
        (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P),
        ∃ (A' : CochainComplex X.Modules ℤ) (q : A' ⟶ A) (a : A' ⟶ P),
          locallyPerfect X A' ∧ QuasiIso ((restrict j).map q) ∧
          (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ α =
            (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map a)) :
    HasDerivedRoofs j := by
  intro A P hA hP α
  obtain ⟨A₀, hA₀, ⟨eA⟩⟩ := hmodels A hA
  obtain ⟨P₀, hP₀, ⟨eP⟩⟩ := hmodels P hP
  let β := (restrictDerivedIso j eA).hom ≫ α ≫ (restrictDerivedIso j eP).inv
  obtain ⟨M, q, a, hM, hq, ha⟩ := hroof A₀ P₀ hA₀ hP₀ β
  obtain ⟨N, s, q', a', hs, hq', ha'⟩ := common_global_right_fraction
    ((DerivedCategory.Q (C := X.Modules)).map q ≫ eA.hom)
      ((DerivedCategory.Q (C := X.Modules)).map a ≫ eP.hom)
  have hN : locallyPerfect X N := (locallyPerfect_iff_of_quasiIso s).mpr hM
  have hqr := congrArg (restrictDerivedHom j) hq'
  have har := congrArg (restrictDerivedHom j) ha'
  simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hqr har
  have hweak : QuasiIso ((restrict j).map q') := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp
    rw [← hqr]
    change IsIso ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map s) ≫
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ (restrictDerivedIso j eA).hom)
    infer_instance
  refine ⟨N, q', a', hN, hweak, ?_⟩
  rw [← hqr, ← har]
  simp only [Category.assoc]
  change (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map s) ≫
    (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ (restrictDerivedIso j eA).hom
      ≫ α =
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map s) ≫
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map a) ≫
          (restrictDerivedIso j eP).hom
  rw [← ha]
  simp only [β, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Quillen.PerfectComplexes.OpenDerivedImage
