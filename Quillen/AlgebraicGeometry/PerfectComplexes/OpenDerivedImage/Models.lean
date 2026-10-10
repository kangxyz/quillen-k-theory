/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Roofs

/-! # Actual global model transport for the open-derived roof interface -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Two specified global derived arrows have one genuine globally weak source
denominator and original chain numerators with exact localization equations. -/
theorem common_global_right_fraction {P A B : Complex X}
    (α : (toDerived X).obj P ⟶ (toDerived X).obj A)
    (β : (toDerived X).obj P ⟶ (toDerived X).obj B) :
    ∃ (M : Complex X) (s : M ⟶ P) (a : M ⟶ A) (b : M ⟶ B),
      QuasiIso s ∧ (toDerived X).map s ≫ α = (toDerived X).map a ∧
      (toDerived X).map s ≫ β = (toDerived X).map b := by
  obtain ⟨M₁, s₁, a₁, hs₁, ha⟩ := toDerived_right_fraction α
  obtain ⟨M₂, s₂, b, hs₂, hb⟩ := toDerived_right_fraction ((toDerived X).map s₁ ≫ β)
  refine ⟨M₂, s₂ ≫ s₁, s₂ ≫ a₁, b, inferInstance, ?_, ?_⟩
  · simp only [Functor.map_comp, Category.assoc, ha]
  · simpa only [Functor.map_comp, Category.assoc] using hb

/-- Actual open roofs on globally chosen models imply the full roof interface.
The final two numerators are obtained by a GLOBAL weak right denominator;
no all-sheaf supported-denominator assertion is used. -/
theorem hasDerivedRoofs_of_models
    (Q : ObjectProperty (Complex X))
    (hmodels : ∀ (P : Complex X), locallyPerfect X P →
      ∃ A : Complex X, Q A ∧ Nonempty ((toDerived X).obj A ≅ (toDerived X).obj P))
    (hroof : ∀ (A P : Complex X), Q A → Q P →
      ∀ α : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj P),
        ∃ (A' : Complex X) (q : A' ⟶ A) (a : A' ⟶ P),
          locallyPerfect X A' ∧ QuasiIso ((restrict j).map q) ∧
          (toDerived U).map ((restrict j).map q) ≫ α = (toDerived U).map ((restrict j).map a)) :
    HasDerivedRoofs j := by
  intro A P hA hP α
  obtain ⟨A₀, hA₀, ⟨eA⟩⟩ := hmodels A hA
  obtain ⟨P₀, hP₀, ⟨eP⟩⟩ := hmodels P hP
  let β := (restrictDerivedIso j eA).hom ≫ α ≫ (restrictDerivedIso j eP).inv
  obtain ⟨M, q, a, hM, hq, ha⟩ := hroof A₀ P₀ hA₀ hP₀ β
  obtain ⟨N, s, q', a', hs, hq', ha'⟩ := common_global_right_fraction
    ((toDerived X).map q ≫ eA.hom) ((toDerived X).map a ≫ eP.hom)
  have hN : locallyPerfect X N := (locallyPerfect_iff_of_quasiIso s).mpr hM
  have hqr := congrArg (restrictDerivedHom j) hq'
  have har := congrArg (restrictDerivedHom j) ha'
  simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hqr har
  have hweak : QuasiIso ((restrict j).map q') := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp
    change IsIso ((toDerived U).map ((restrict j).map q'))
    rw [← hqr]
    change IsIso ((toDerived U).map ((restrict j).map s) ≫
      (toDerived U).map ((restrict j).map q) ≫ (restrictDerivedIso j eA).hom)
    infer_instance
  refine ⟨N, q', a', hN, hweak, ?_⟩
  rw [← hqr, ← har]
  simp only [Category.assoc]
  change (toDerived U).map ((restrict j).map s) ≫
    (toDerived U).map ((restrict j).map q) ≫ (restrictDerivedIso j eA).hom ≫ α =
      (toDerived U).map ((restrict j).map s) ≫
        (toDerived U).map ((restrict j).map a) ≫ (restrictDerivedIso j eP).hom
  rw [← ha]
  simp only [β, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Quillen.PerfectComplexes.OpenDerivedImage
