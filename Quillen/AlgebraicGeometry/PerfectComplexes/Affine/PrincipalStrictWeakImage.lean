/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.StrictOpenRelative
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalMapFactorization
public import Quillen.Waldhausen.Approximation.WeakImageKEquivalence

/-! # Genuine principal strict approximation onto the witnessed restriction image

The actual geometric principal-open map factorization supplies restricted
App2, with no map-lifting premise. Original relative reflection and the actual
strict cone cylinder discharge the remaining approximation inputs. The
unchanged original S-map is completely weak, and its canonical K-map is
bijective in every connective degree onto the constructed strict image.
Strict/all-perfect comparison and image-inclusion cofinality remain separate.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.PerfectComplexes.StrictOpenWeakImage
open Waldhausen
variable (R : CommRingCat.{u}) (r : R)

/-- Genuine principal-open geometric factorization proves restricted App2;
no map-factorization or approximation hypothesis is supplied. -/
theorem principal_approximationOnImage : ApproximationImage.HasApproximationOnImage
    (coarseWaldhausen (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))
      (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) :=
  ApproximationImage.HasApproximationOnImage.of_factorization _ _ _
    (sourceFactorization (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))
    (restriction_exact (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).weak (fun
      _ hf ↦ hf)
    (fun f hB ↦ by
      obtain ⟨E, q, hq⟩ := hB
      exact Affine.exists_principal_strict_map_factorization R r f E q hq)

/-- The actual full category of strict targets with a weak original restriction witness. -/
abbrev PrincipalObj := ApproximationImage.Obj (strictWaldhausen _)
  (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))

/-- Its inherited Waldhausen structure is proved from genuine principal map replacement. -/
def principalWaldhausen : Structure (PrincipalObj R r) :=
  ApproximationImage.waldhausenStructure (principal_approximationOnImage R r)
    (restriction_exact (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))

/-- Original strict restriction corestricts exactly to the actual constructed image. -/
theorem principalCorestrict_exact : IsExact
    (coarseWaldhausen (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).cof
    (coarseWaldhausen (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).weq
    (principalWaldhausen R r).cof (principalWaldhausen R r).weq
    (ApproximationImage.corestrict (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))) :=
  ApproximationImage.corestrict_exact (principal_approximationOnImage R r)
    (restriction_exact (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))

/-- The original inclusion of the actual witnessed strict image is exact. -/
theorem principalInclusion_exact : IsExact (principalWaldhausen R r).cof (principalWaldhausen R
  r).weq
    (strictWaldhausen _).cof (strictWaldhausen _).weq
    (ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))).ι :=
  ApproximationImage.inclusion_exact (principal_approximationOnImage R r)
    (restriction_exact (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))

/-- Complete weakness of the literal original principal strict corestriction S-map. -/
theorem principal_deloopingMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (deloopingMap (principalCorestrict_exact R r)).hom := by
  let : (strictWaldhausen (Spec (.of (Localization.Away r)))).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (subcategoryWeakEquivalences (strictPerfect _)).HasTwoOutOfThreeProperty
  exact ApproximationImage.corestrict_deloopingMap_isWeakHomotopyEquivalence
    (principal_approximationOnImage R r) (restriction_exact
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))
    (coarseJointData (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))

/-- Actual principal strict relative approximation, on every original connective K-map. -/
def principalKEquiv (n : ℕ) : (coarseWaldhausen
  (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).K n ≃*
    (principalWaldhausen R r).K n :=
  KEquivOfWeakRealization (principalCorestrict_exact R r)
    (principal_deloopingMap_isWeakHomotopyEquivalence R r) n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem principalKEquiv_coe (n : ℕ) :
    ↑(principalKEquiv R r n) = KMap (principalCorestrict_exact R r) n := rfl

/-- Composing the equivalence with image inclusion recovers actual relative restriction. -/
theorem principalInclusion_comp_corestrict (n : ℕ) :
    (KMap (principalInclusion_exact R r) n).comp (KMap (principalCorestrict_exact R r) n) =
      relativeKRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) n :=
  ApproximationImage.inclusion_KMap_comp_corestrict (principal_approximationOnImage R r)
    (restriction_exact (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) n

end Quillen.PerfectComplexes.StrictOpenWeakImage
