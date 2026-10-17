/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.RingTheory.RegularLocalRing.AffineProjectiveDimension

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Regular.LocalLowDimension
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Canonical K-to-G comparison for regular affine schemes of dimension at most one

Every prime localization of a regular ring of dimension at most one is a
regular local ring of dimension at most one, hence a PID by the proved local
argument. Actual finite-module projective dimension is at most one locally,
therefore globally. This gives actual finite vector-bundle resolutions and
the canonical Quillen comparison.
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

/-- For a regular Noetherian ring of dimension at most one, the existing
canonical vector-bundle K-to-coherent G comparison is bijective in every
nonnegative degree. -/
theorem KToG_regular_dimension_le_one_bijective (R : CommRingCat.{u}) [IsRegularRing R]
    (hd : ringKrullDim R ≤ 1) (n : ℕ) : Function.Bijective (KToG (Spec R) n) := by
  apply AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_length_one (Spec R) _ n
  intro M
  have :=
    AlgebraicGeometry.Scheme.Modules.Coherent.hasProjectiveDimensionLE_one_of_regular_dim_le_one R
    hd
    ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
      R).functor.obj M).obj
  exact AlgebraicGeometry.Scheme.Modules.coherentResolution_length_le_of_projectiveDimensionLE R 1 M

/-- The actual canonical equivalence for a regular affine ring of dimension
at most one. The forward homomorphism is the existing `Scheme.KToG`. -/
def KToGRegularDimOneEquiv (R : CommRingCat.{u}) [IsRegularRing R]
    (hd : ringKrullDim R ≤ 1) (n : ℕ) : K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_regular_dimension_le_one_bijective R hd n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGRegularDimOneEquiv_coe (R : CommRingCat.{u}) [IsRegularRing R]
    (hd : ringKrullDim R ≤ 1) (n : ℕ) :
    ↑(KToGRegularDimOneEquiv R hd n) = KToG (Spec R) n := rfl

end AlgebraicGeometry.Scheme
