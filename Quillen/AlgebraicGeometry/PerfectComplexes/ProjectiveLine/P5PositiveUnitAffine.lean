/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackPushforward
public import Aglib.AlgebraicGeometry.Cohomology.Godement.PullbackPushforward
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.Strictification
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.GodementUnit

/-! # The actual positive unit on all affine perfect bounded-below complexes

The canonical cochain map is the original geometric adjunction unit followed
by direct image of the original Godement augmentation. Its localized natural
transformation transports the proved bounded-bundle calculation through a
genuine affine derived representative; target terms need not be quasicoherent.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance positiveUnitStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The original affine strict positive unit is retained literally. -/
lemma positivePlusUnit_affine (R : CommRingCat.{u}) (K : CochainComplex.Plus (Spec R).Modules) :
    (AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit (projection R)).app K =
      (StrictPositiveRetraction.positivePlusUnit R).app K := rfl

/-- Actual affine perfect complexes have the same canonical weak unit without term-QC premises. -/
theorem positivePlusUnit_affine_quasiIso (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (hK : locallyPerfect (Spec R) K.obj) :
    QuasiIso ((AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit (projection
      R)).app K).hom := by
  obtain ⟨P, ⟨eP⟩⟩ := Affine.locallyPerfect_exists_strictPerfect_representative R hK
  let A := (strictToPlus (Spec R)).obj P
  let e : DerivedCategory.Plus.Q.obj A ≅ DerivedCategory.Plus.Q.obj K :=
    DerivedCategory.Plus.ι.preimageIso eP
  have hA : QuasiIso ((AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit
    (projection R)).app A).hom := by
    rw [positivePlusUnit_affine]
    obtain ⟨a, b, hab⟩ := P.property.1
    exact StrictPositiveRetraction.positivePlusUnit_quasiIso R A a b
      (fun i hi => hab i (Or.inl hi)) (fun i hi => hab i (Or.inr hi)) P.property.2
  have hD : IsIso ((AlgebraicGeometry.Scheme.Modules.derivedPullbackPushforwardPlusUnit (projection
    R)).app (DerivedCategory.Plus.Q.obj A)) := by
    rw [AlgebraicGeometry.Scheme.Modules.derivedPullbackPushforwardPlusUnit_app]
    exact AlgebraicGeometry.Scheme.Modules.Godement.isIso_derivedUnit_of_quasiIso_unit (projection
      R) A hA
  exact AlgebraicGeometry.Scheme.Modules.Godement.quasiIso_unit_of_isIso_derivedUnit (projection R)
    K
    ((NatTrans.isIso_app_iff_of_iso
      (AlgebraicGeometry.Scheme.Modules.derivedPullbackPushforwardPlusUnit (projection R)) e).mp hD)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit
