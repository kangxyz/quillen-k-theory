/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedHomVanishing

/-! # Original affine vanishing consumers, including torsion targets and degenerate localization -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
namespace QuillenTest.AffineDerivedHomVanishing

open Quillen

/-- A nonprojective torsion single is permitted as target over the integers. -/
theorem original_torsion_target (P : ModuleComplex (CommRingCat.of ℤ))
    (hP : moduleStrictPerfect (CommRingCat.of ℤ) P) (b : ℤ)
    (hbound : ∀ i, i < b → IsZero (P.X i))
    (φ : (toDerived (Spec (.of ℤ))).obj ((associatedComplex (.of ℤ)).obj P) ⟶
      (toDerived (Spec (.of ℤ))).obj ((_root_.CochainComplex.singleFunctor
        (Spec (.of ℤ)).Modules (b-1)).obj (tilde (ModuleCat.of ℤ (ZMod 2))))) : φ = 0 :=
  associatedComplex_derivedHom_single_eq_zero (.of ℤ) P hP _ (b-1) b hbound (by omega) φ

/-- Even localization at zero retains the original source lower bound and exact endpoint. -/
theorem original_zero_localization (R : CommRingCat.{u}) (P : ModuleComplex R)
    (hP : moduleStrictPerfect R P)
    (M : (Spec (CommRingCat.of (Localization.Away (0 : R)))).Modules) [M.IsQuasicoherent]
    (b : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i))
    (φ : (toDerived (Spec (.of (Localization.Away (0 : R))))).obj
        ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R 0)).obj
          ((associatedComplex R).obj P)) ⟶
      (toDerived (Spec (.of (Localization.Away (0 : R))))).obj
        ((_root_.CochainComplex.singleFunctor (Spec (.of (Localization.Away (0 : R)))).Modules
          (b-1)).obj M)) :
    φ = 0 :=
  principalRestriction_associated_derivedHom_single_eq_zero R 0 P hP M (b-1) b hbound (by omega) φ

/-- The adjacent cutoff is shifted by precisely n for every integer source shift. -/
theorem original_shifted_adjacent_cutoff (R : CommRingCat.{u}) (P : Complex (Spec R))
    (hP : strictPerfect (Spec R) P) (M : (Spec R).Modules) [M.IsQuasicoherent]
    (b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i))
    (φ : ((toDerived (Spec R)).obj P)⟦n⟧ ⟶ (toDerived (Spec R)).obj
      ((_root_.CochainComplex.singleFunctor (Spec R).Modules (b-n-1)).obj M)) : φ = 0 :=
  strictPerfect_derivedHom_single_shift_eq_zero R P hP M (b-n-1) b n hbound (by omega) φ

/-- Only the supplied genuine module model is bounded; the original ambient source is arbitrary. -/
theorem original_arbitrary_source_model (R : CommRingCat.{u}) (E : Complex (Spec R))
    (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (e : (toDerived (Spec R)).obj ((associatedComplex R).obj P) ≅ (toDerived (Spec R)).obj E)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (a b : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a < b)
    (φ : (toDerived (Spec R)).obj E ⟶ (toDerived (Spec R)).obj
      ((_root_.CochainComplex.singleFunctor (Spec R).Modules a).obj M)) :
    φ = 0 ∧ e.hom ≫ φ = 0 := by
  have h := derivedHom_single_eq_zero_of_module_model R _ P hP e M a b hbound hab φ
  exact ⟨h, by rw [h, comp_zero]⟩

end QuillenTest.AffineDerivedHomVanishing
