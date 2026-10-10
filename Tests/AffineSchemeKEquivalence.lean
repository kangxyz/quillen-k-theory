/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Affine.SchemeKEquivalence

/-! # Presentation-independent affine comparisons and inverse functoriality -/
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.Tests.AffineSchemeKEquivalence
open PerfectComplexes

/-- The presentation-independent comparison recovers the original spectrum comparison. -/
theorem original_spectrum_equiv (R : CommRingCat.{u}) (n : ℕ) :
    affineStrictToPerfectKEquiv (Spec R) n = Affine.strictToPerfectKEquiv R n := rfl

/-- No chosen affine presentation is needed for a unique original public K₀ lift. -/
theorem affine_public_unique_lift (X : Scheme.{u}) [IsAffine X] (x : PerfectK X 0) :
    ∃! a : Quillen.Scheme.K X 0, vectorBundleToPerfectKMap X 0 a = x :=
  (vectorBundleToPerfectKMap_bijective_of_isAffine X 0).existsUnique x

/-- Inverse pullback compatibility holds on every actual affine morphism at K₀. -/
theorem original_public_inverse_pullback {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (x : PerfectK Y 0) :
    Quillen.Scheme.pullbackK f 0 ((affineVectorBundleToPerfectKEquiv Y 0).symm x) =
      (affineVectorBundleToPerfectKEquiv X 0).symm (perfectKPullback f 0 x) :=
  (affineVectorBundleToPerfectKEquiv_symm_pullback f 0 x).symm

/-- The inverse strict comparison retains composition of the actual pullback maps. -/
theorem original_inverse_composite {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (x : PerfectK Z n) :
    (affineStrictToPerfectKEquiv X n).symm (perfectKPullback (f ≫ g) n x) =
      strictKPullback f n (strictKPullback g n ((affineStrictToPerfectKEquiv Z n).symm x)) := by
  rw [affineStrictToPerfectKEquiv_symm_pullback, strictKPullback_comp]
  rfl

/-- Actual perfect classes transport uniquely along the canonical spectrum isomorphism. -/
theorem canonical_spectrum_unique_pullback (X : Scheme.{u}) [IsAffine X] (n : ℕ)
    (x : PerfectK X n) :
    ∃! y : PerfectK (Spec Γ(X, ⊤)) n, perfectKPullback X.isoSpec.hom n y = x :=
  (perfectKPullback_iso_bijective X.isoSpec n).existsUnique x
end Quillen.Tests.AffineSchemeKEquivalence
