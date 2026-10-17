/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.RingTheory.RegularLocalRing.AffineProjectiveDimension

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.Aglib.RingTheory.RegularLocalRing.ProjectiveDimension
public import Quillen.AlgebraicGeometry.Scheme.Regular.GeneralComparison
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Canonical K-to-G equivalence for finite-dimensional regular affine schemes

Regular local finite-projective-dimension bounds are proved from actual
regularity, and localization carries them to finite modules over the original
regular ring. The genuine finite resolutions feed Quillen's proved general
resolution theorem. No K-equivalence or resolution theorem is assumed.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme

/-- The canonical K-to-G comparison for a regular ring with a stated finite
dimension bound, in every nonnegative degree. Every homological hypothesis
is discharged from regularity and the dimension bound. -/
theorem KToG_regular_dimension_le_bijective (R : CommRingCat.{u}) [IsRegularRing R]
    (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ)) (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) := by
  apply AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_finite_resolutions (Spec R) _ n
  apply AlgebraicGeometry.Scheme.Modules.coherentResolutionHypothesis_of_finite_projectiveDimension
    R
  intro M
  exact (projectiveDimension_ne_top_iff M.obj).mpr
    ⟨d, AlgebraicGeometry.Scheme.Modules.Coherent.hasProjectiveDimensionLE_of_regular_dimension_le R
      d hd M.obj⟩

/-- The actual canonical comparison packaged as an equivalence. -/
def KToGRegularFiniteDimensionEquiv (R : CommRingCat.{u}) [IsRegularRing R]
    (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ)) (n : ℕ) : K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_regular_dimension_le_bijective R d hd n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGRegularFiniteDimensionEquiv_coe (R : CommRingCat.{u}) [IsRegularRing R]
    (d : ℕ) (hd : ringKrullDim R ≤ (d : ℕ)) (n : ℕ) :
    ↑(KToGRegularFiniteDimensionEquiv R d hd n) = KToG (Spec R) n := rfl

/-- The conventional finite-Krull-dimension typeclass also supplies the
canonical regular-affine comparison, with no chosen numerical bound. -/
theorem KToG_regular_finiteDimension_bijective (R : CommRingCat.{u}) [IsRegularRing R]
    [FiniteRingKrullDim R] (n : ℕ) : Function.Bijective (KToG (Spec R) n) := by
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have hat : a ≠ ⊤ := by
    intro h
    exact ringKrullDim_ne_top (R := R) (ha.symm.trans (by rw [h]; rfl))
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hat
  apply KToG_regular_dimension_le_bijective R d _ n
  exact le_of_eq (by rw [← ha, ← hd]; rfl)

end AlgebraicGeometry.Scheme
