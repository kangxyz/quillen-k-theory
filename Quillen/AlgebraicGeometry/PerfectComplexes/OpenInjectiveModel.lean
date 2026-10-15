/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ComplexPushforward
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.Factorizations.CM5a
/-!
# Actual injective direct-image models across open immersions

An original cohomologically lower-bounded complex maps quasi-isomorphically
into the restriction of an actual lower-bounded injective complex on the
ambient scheme. This is the genuine direct image of a constructed injective
replacement, using exact restriction and its original fully faithful right
adjoint. Quasi-compact perfect complexes supply the needed lower bound.

No exactness of ordinary direct image, ambient quasicoherence, upper bound,
or ambient perfection is asserted. The derived counit alone does not prove
these additional properties.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.PerfectComplexes
/-- The standard derived model used for the original open pushforward comparisons. -/
local instance openPushforwardStandardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules
  :=
  HasDerivedCategory.standard _

/-- Restricting the original termwise direct image gives the original counit. -/
def pushforwardComplexRestrictIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    pushforwardComplex j ⋙ restrict j ≅ 𝟭 (Complex U) :=
  Functor.mapHomologicalComplexCompIso (Scheme.Modules.restrictFunctorAdjCounitIso j) _ ≪≫
    Functor.mapHomologicalComplexIdIso U.Modules _

/-- The actual right adjoint preserves injective module sheaves because restriction is exact. -/
theorem injective_pushforward {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) [Injective M] : Injective ((Scheme.Modules.pushforward j).obj M) :=
  (Scheme.Modules.restrictAdjunction j).map_injective M inferInstance

/-- A genuine original quasi-isomorphism into the restriction of a lower-bounded
injective direct-image complex. No quasicoherence or upper bound is asserted. -/
theorem exists_open_injective_quasiIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : Complex U) (a : ℤ) [E.IsGE a] :
    ∃ (J : Complex X) (q : E ⟶ (restrict j).obj J),
      J.IsStrictlyGE a ∧ (∀ n : ℤ, Injective (J.X n)) ∧ QuasiIso q := by
  have : QuasiIso (E.πTruncGE a) := (E.quasiIso_πTruncGE_iff a).mpr inferInstance
  obtain ⟨I,s,hs,hI,hIa⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (E.truncGE a) a
  let := hs
  let := hIa
  let J := (pushforwardComplex j).obj I
  let q : E ⟶ (restrict j).obj J :=
    E.πTruncGE a ≫ s ≫ ((pushforwardComplexRestrictIso j).app I).inv
  refine ⟨J, q, ?_, ?_, ?_⟩
  · dsimp [J, pushforwardComplex]
    infer_instance
  · intro n
    let := hI n
    exact injective_pushforward j (I.X n)
  · dsimp [q]
    infer_instance

/-- The actual original derived value is recovered after restriction. -/
theorem exists_open_injective_model {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : Complex U) (a : ℤ) [E.IsGE a] :
    ∃ J : Complex X, J.IsStrictlyGE a ∧ (∀ n : ℤ, Injective (J.X n)) ∧
      Nonempty ((toDerived U).obj ((restrict j).obj J) ≅ (toDerived U).obj E) := by
  obtain ⟨J, q, hJ, hI, hq⟩ := exists_open_injective_quasiIso j E a
  let := hq
  exact ⟨J, hJ, hI, ⟨(asIso ((toDerived U).map q)).symm⟩⟩

/-- Quasi-compactness supplies a genuine lower bound for each original perfect
complex. The ambient injective model is not claimed perfect or quasicoherent. -/
theorem exists_perfect_open_injective_quasiIso {U X : Scheme.{u}} [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (E : Perfect U) :
    ∃ (a : ℤ) (J : Complex X) (q : E.obj ⟶ (restrict j).obj J),
      J.IsStrictlyGE a ∧ (∀ n : ℤ, Injective (J.X n)) ∧ QuasiIso q := by
  obtain ⟨a, b, hab⟩ := locallyPerfect_homology_bounded E.property
  have : E.obj.IsGE a := (CochainComplex.isGE_iff E.obj a).mpr
    (fun n hn => (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hab n (Or.inl hn)))
  obtain ⟨J, q, hJ, hI, hq⟩ := exists_open_injective_quasiIso j E.obj a
  exact ⟨a, J, q, hJ, hI, hq⟩
end Quillen.PerfectComplexes
