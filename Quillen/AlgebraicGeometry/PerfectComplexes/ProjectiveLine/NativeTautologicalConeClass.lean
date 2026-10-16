/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeRankOneClass
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeAffineTautological
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoordinateCone
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# The original affine coordinate cone and its unchanged native Phi class

Transport the actual native endpoints through the original affine scheme pullback
and tautological-line isomorphism. The signed cone class is Phi(e,e⁻¹) under the
existing Phi, where e is the rank-one object class. Actual inverse pullback cancels
by the original composition and identity laws; no new equivalence is assumed.
No boundary or excision identity is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- The original native affine tautological comparison on the actual perfect singles. -/
def nativeAffineTautologicalPerfectIso (R : CommRingCat.{u}) :
    (perfectFlatPullback (nativeAffineIso R).hom).obj
      (nativeTautologicalPerfect ⟨Spec R, inferInstance⟩) ≅ tautologicalPerfect R :=
  (locallyPerfect _).isoMk
    (((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pullback (nativeAffineIso R).hom) (.up ℤ) 0).app
        (nativeTautologicalLine ⟨Spec R, inferInstance⟩)) ≪≫
      (CochainComplex.singleFunctor (twoChartLine R).Modules 0).mapIso
        (nativeAffineTautologicalIso R))

/-- Actual affine pullback of the original first summand has the original structure endpoint. -/
def nativeFirstRankOneTransportIso (R : CommRingCat.{u}) :
    (perfectFlatPullback (nativeAffineIso R).hom).obj
      ((nativeFirstSummand ⟨Spec R, inferInstance⟩).obj (rankOnePerfect (Spec R))) ≅
        rankOnePerfect (twoChartLine R) :=
  (perfectFlatPullback (nativeAffineIso R).hom).mapIso
    (nativeFirstRankOneIso ⟨Spec R, inferInstance⟩) ≪≫
      rankOnePerfectFlatPullbackIso (nativeAffineIso R).hom

/-- Actual affine pullback of the unchanged left-tensor second summand retains O(-1). -/
def nativeSecondRankOneTransportIso (R : CommRingCat.{u}) :
    (perfectFlatPullback (nativeAffineIso R).hom).obj
      ((nativeSecondSummand ⟨Spec R, inferInstance⟩).obj (rankOnePerfect (Spec R))) ≅
        tautologicalPerfect R :=
  (perfectFlatPullback (nativeAffineIso R).hom).mapIso
    (nativeSecondRankOneIso ⟨Spec R, inferInstance⟩) ≪≫
      nativeAffineTautologicalPerfectIso R

/-- The actual inverse affine pullback cancels by the original geometric K-map laws. -/
theorem nativeAffineKMap_inverse (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).inv n).comp
      (perfectKFlatPullback (nativeAffineIso R).hom n) =
        MonoidHom.id (PerfectK (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj n) := by
  rw [← perfectKFlatPullback_comp]
  simpa only [Iso.inv_hom_id] using
    perfectKFlatPullback_id (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj n

/-- Forward affine transport of the unchanged Phi coordinates is the actual signed local cone. -/
theorem nativePhi_rankOne_difference_transport (R : CommRingCat.{u}) :
    perfectKFlatPullback (nativeAffineIso R).hom 0
      (nativeTwoSummandKMap ⟨Spec R, inferInstance⟩ 0
        ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)),
          ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹)) =
      (perfectWaldhausen (twoChartLine R)).kZeroObjectClass
        ⟨(tautologicalCoordinateSupportedCone R).obj,
          (tautologicalCoordinateSupportedCone R).property.1⟩ := by
  rw [nativeTwoSummandKMap_apply]
  simp only [perfectKFlatPullback, map_mul, map_inv, KMap_kZeroObjectClass]
  rw [(perfectWaldhausen _).kZeroObjectClass_iso (nativeFirstRankOneTransportIso R),
    (perfectWaldhausen _).kZeroObjectClass_iso (nativeSecondRankOneTransportIso R)]
  exact (SplitFactorization.subcategoryCone_kZeroObjectClass (locallyPerfect _)
    (fun hK hL g => locallyPerfect_mappingCone hK hL g)
    (tautologicalCoordinatePerfect R)).symm

/-- The actual inverse-affine restriction of the original coordinate cone has precisely the
original Phi coordinates (rank one, inverse rank one), with no alternate coordinate equivalence. -/
theorem inverseAffineTautologicalCone_class (R : CommRingCat.{u}) :
    (perfectWaldhausen (nativeLineFunctor.obj ⟨Spec R, inferInstance⟩).obj).kZeroObjectClass
      ((perfectRestrict (nativeAffineIso R).inv).obj
        ⟨(tautologicalCoordinateSupportedCone R).obj,
          (tautologicalCoordinateSupportedCone R).property.1⟩) =
      nativeTwoSummandKMap ⟨Spec R, inferInstance⟩ 0
        ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)),
          ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹) := by
  have h := congrArg (perfectKFlatPullback (nativeAffineIso R).inv 0)
    (nativePhi_rankOne_difference_transport R)
  have hi := DFunLike.congr_fun (nativeAffineKMap_inverse R 0)
    (nativeTwoSummandKMap ⟨Spec R, inferInstance⟩ 0
      ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)),
        ((perfectWaldhausen (Spec R)).kZeroObjectClass (rankOnePerfect (Spec R)))⁻¹))
  change perfectKFlatPullback (nativeAffineIso R).inv 0
    (perfectKFlatPullback (nativeAffineIso R).hom 0 _) = _ at hi
  rw [hi, perfectKFlatPullback_eq_restrict] at h
  exact (h.trans (KMap_kZeroObjectClass (perfectRestrict_waldhausenExact
    (nativeAffineIso R).inv) _)).symm

end Quillen.PerfectComplexes.ProjectiveLine
