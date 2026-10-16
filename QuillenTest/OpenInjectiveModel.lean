/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.OpenInjectiveModel
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Genuine injective extension consumers -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.PerfectComplexes


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.OpenInjectiveModel

open Quillen
open PerfectComplexes

/-- The original counit has the literal inverse equations on the original complex. -/
theorem actual_counit_inverse {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : CochainComplex U.Modules ℤ) :
    ((pushforwardComplexRestrictIso j).app I).inv ≫
      ((pushforwardComplexRestrictIso j).app I).hom = 𝟙 I := by simp

/-- No termwise lower bound is imposed on the input to recover its original derived value. -/
theorem original_derived_value {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : CochainComplex U.Modules ℤ) (a : ℤ) [E.IsGE a] :
    ∃ J : CochainComplex X.Modules ℤ, J.IsStrictlyGE a ∧ (∀ n : ℤ, Injective (J.X n)) ∧
      Nonempty ((DerivedCategory.Q (C := U.Modules)).obj E ≅
        (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj J)) := by
  obtain ⟨J, hJ, hI, ⟨e⟩⟩ := exists_open_injective_model j E a
  exact ⟨J, hJ, hI, ⟨e.symm⟩⟩

/-- Every original perfect complex on a quasi-compact open has the original
quasi-isomorphism into the restricted model, retaining local perfection there. -/
theorem perfect_restricted_model {U X : Scheme.{u}} [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (E : Perfect U) :
    ∃ (a : ℤ) (J : CochainComplex X.Modules ℤ) (q : E.obj ⟶ (restrict j).obj J),
      J.IsStrictlyGE a ∧ (∀ n : ℤ, Injective (J.X n)) ∧ QuasiIso q ∧
      locallyPerfect U ((restrict j).obj J) := by
  obtain ⟨a, J, q, hJ, hI, hq⟩ := exists_perfect_open_injective_quasiIso j E
  let := hq
  exact ⟨a, J, q, hJ, hI, hq, (locallyPerfect_iff_of_quasiIso q).mp E.property⟩

/-- The actual ambient terms are injective, rather than merely locally injective. -/
theorem actual_term_extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) [Injective M] : Injective ((Scheme.Modules.pushforward j).obj M) :=
  injective_pushforward j M
end QuillenTest.OpenInjectiveModel
