/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalConnectingNaturality

/-! # Original principal localization naturality consumers -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
universe u
namespace QuillenTest.PrincipalConnectingNaturality
variable {R S : CommRingCat.{u}} {r : R} {s : S}

/-- The actual K₁ boundary has the original supported K₀ pullback. -/
theorem original_K1_K0_boundary (f : principalOpenPair R r ⟶ principalOpenPair S s)
    (x : PerfectK (Spec (.of (Localization.Away s))) 1) :
    perfectSupportedKPullback f 0 (principalPerfectConnectingHom S s 0 x) =
      principalPerfectConnectingHom R r 0 (perfectKPullback f.hom.hom.left 1 x) :=
  DFunLike.congr_fun (principalPerfectConnectingHom_pullback f 0) x

/-- A vanishing original extension obstruction remains zero after any allowed pair pullback. -/
theorem original_principal_obstruction_preserved (f : principalOpenPair R r ⟶ principalOpenPair S s)
    (n : ℕ) (x : PerfectK (Spec (.of (Localization.Away s))) (n+1))
    (hx : principalPerfectConnectingHom S s n x = 1) :
    principalPerfectConnectingHom R r n (perfectKPullback f.hom.hom.left (n+1) x) = 1 := by
  exact (DFunLike.congr_fun (principalPerfectConnectingHom_pullback f n) x).symm.trans
    ((congrArg (perfectSupportedKPullback f n) hx).trans (map_one _))

/-- Actual extendibility of a positive class is preserved, using the original boundary and LES. -/
theorem original_extendible_class_pulls_back (f : principalOpenPair R r ⟶ principalOpenPair S s)
    (n : ℕ) (x : PerfectK (Spec (.of (Localization.Away s))) (n+1))
    (hx : x ∈ (perfectKRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen S s)
      (n+1)).range) :
    perfectKPullback f.hom.hom.left (n+1) x ∈
      (perfectKRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
        (n+1)).range := by
  rw [range_principal_perfectKRestrict_eq_ker_principalPerfectConnectingHom] at hx ⊢
  exact original_principal_obstruction_preserved f n x hx

end QuillenTest.PrincipalConnectingNaturality
