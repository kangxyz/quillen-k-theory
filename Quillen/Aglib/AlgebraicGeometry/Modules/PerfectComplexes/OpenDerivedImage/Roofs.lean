/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Basic
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.EqualityDenominators
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
/-! # Actual global-model roofs and genuine original weak homotopy roofs

The sole geometric input is the exact locally weak global-model roof property.
All-sheaf target homotopies follow from actual localization denominators.
-/
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

/-- The geometric roof input only involves two globally perfect models.
Its denominator is required weak on the original open, not globally weak. -/
def HasDerivedRoofs : Prop :=
  ∀ (A P : CochainComplex X.Modules ℤ), locallyPerfect X A → locallyPerfect X P →
    ∀ α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P),
      ∃ (A' : CochainComplex X.Modules ℤ) (q : A' ⟶ A) (a : A' ⟶ P),
        locallyPerfect X A' ∧ QuasiIso ((restrict j).map q) ∧
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ α =
          (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map a)

/-- Genuine module/geometric roofs between global models give a complete
original homotopy roof for arbitrary sheaf-complex targets. The remaining
all-sheaf denominators are legitimate localization denominators only. -/
theorem exists_homotopy_roof (hroof : HasDerivedRoofs j)
    (P : CochainComplex X.Modules ℤ) (hP : locallyPerfect X P) (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j B') (w : (restrict j).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (A : CochainComplex X.Modules ℤ) (M N : CochainComplex U.Modules ℤ)
      (a : A ⟶ P) (p : (restrict j).obj A ⟶ M) (t : B' ⟶ M)
      (s : B ⟶ N) (q : M ⟶ N),
      locallyPerfect X A ∧ locallyPerfect U M ∧ locallyPerfect U N ∧
      QuasiIso p ∧ QuasiIso t ∧ QuasiIso s ∧
      Nonempty (Homotopy (p ≫ q) ((restrict j).map a ≫ w ≫ s)) ∧
      Nonempty (Homotopy (t ≫ q) (b ≫ s)) := by
  obtain ⟨A₀, M, p₀, t, hA₀, hM, hp₀, ht⟩ := exists_weak_cospan j hB'
  let D := DerivedCategory.Q (C := U.Modules)
  let β : D.obj M ⟶ D.obj B := inv (D.map t) ≫ D.map b
  let α : D.obj ((restrict j).obj A₀) ⟶ D.obj ((restrict j).obj P) :=
    D.map p₀ ≫ β ≫ inv (D.map w)
  obtain ⟨A, r, a, hA, hr, ha⟩ := hroof A₀ P hA₀ hP α
  let p := (restrict j).map r ≫ p₀
  have hp : QuasiIso p := inferInstance
  obtain ⟨N, q, s, hDenIso1, hFac1⟩ := DerivedCategory.left_fac β
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso1
  have he : (β) ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map q := by
    let := hDenIso1
    rw [hFac1, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hB : locallyPerfect U B := (locallyPerfect_iff_of_quasiIso w).mp (locallyPerfect_restrict j
    hP)
  have hN : locallyPerfect U N := (locallyPerfect_iff_of_quasiIso s).mp hB
  change D.map ((restrict j).map r) ≫ α = D.map ((restrict j).map a) at ha
  change β ≫ D.map s = D.map q at he
  have heq₁ : D.map (p ≫ q) = D.map ((restrict j).map a ≫ w ≫ s) := by
    simp only [Functor.map_comp]
    rw [← ha, ← he]
    simp [p, α, Category.assoc]
  have heq₂ : D.map (t ≫ q) = D.map (b ≫ s) := by
    rw [Functor.map_comp, ← he]
    simp [β]
  obtain ⟨N', z, hz, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    Quillen.CochainComplex.exists_post_quasiIso_two_homotopies_of_derived_eq
      (C := U.Modules) (p ≫ q) ((restrict j).map a ≫ w ≫ s)
      (t ≫ q) (b ≫ s) heq₁ heq₂
  exact ⟨A, M, N', a, p, t, s ≫ z, q ≫ z, hA, hM,
    (locallyPerfect_iff_of_quasiIso z).mp hN, hp, ht, inferInstance,
    ⟨by simpa only [Category.assoc] using H₁⟩,
    ⟨by simpa only [Category.assoc] using H₂⟩⟩

end Quillen.PerfectComplexes.OpenDerivedImage
