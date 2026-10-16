/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.RankOneFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTwoSummands
public import Quillen.Waldhausen.SplitComplexes.MappingConeKZeroRelation
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Actual native rank-one endpoints and the signed cone coordinate

The original first summand on rank one is the structure single. The original second
summand, with its unchanged left tensor order, is the single of the native tautological
negative line. Thus the existing native Phi sends (e,e⁻¹) to the signed class of any
actual arrow from that negative line to the structure single. No boundary or excision
identification is asserted.
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

/-- The actual native tautological O(-1), as its degree-zero perfect single. -/
def nativeTautologicalPerfect (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    Perfect (nativeLineFunctor.obj X).obj :=
  ⟨(CochainComplex.singleFunctor (nativeLineFunctor.obj X).obj.Modules 0).obj
      (nativeTautologicalLine X),
    locallyPerfect_of_strictPerfect (single_strictPerfect_int _ 0)⟩

/-- The original first native summand on rank one is the original structure single. -/
def nativeFirstRankOneIso (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    (nativeFirstSummand X).obj (rankOnePerfect X.obj) ≅
      rankOnePerfect (nativeLineFunctor.obj X).obj :=
  rankOnePerfectFlatPullbackIso (nativeProjection.app X).hom

/-- The original left tensor of rank one with O(-1) is the original negative-line single. -/
def nativeNegativeTwistRankOneIso (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    (nativeNegativeTwist X).obj (rankOnePerfect (nativeLineFunctor.obj X).obj) ≅
      nativeTautologicalPerfect X :=
  (locallyPerfect _).isoMk
    (((HomologicalComplex.singleMapHomologicalComplex
      (moduleTensorLeftFunctor (nativeLineFunctor.obj X).obj (nativeTautologicalLine X))
        (.up ℤ) 0).app (SheafOfModules.unit (nativeLineFunctor.obj X).obj.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor (nativeLineFunctor.obj X).obj.Modules 0).mapIso
        ((SheafOfModulesOfCommRing.tensorRightUnitIso
          (nativeLineFunctor.obj X).obj.sheaf).app (nativeTautologicalLine X)))

/-- The second original summand retains the actual native negative line, without swapping tensor. -/
def nativeSecondRankOneIso (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    (nativeSecondSummand X).obj (rankOnePerfect X.obj) ≅ nativeTautologicalPerfect X :=
  (nativeNegativeTwist X).mapIso (nativeFirstRankOneIso X) ≪≫
    nativeNegativeTwistRankOneIso X

/-- The original first K-map sends the rank-one coefficient to the native structure class. -/
theorem nativeFirstRankOne_class (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    KMap (nativeFirstSummand_exact X) 0 ((perfectWaldhausen X.obj).kZeroObjectClass
      (rankOnePerfect X.obj)) =
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
        (rankOnePerfect (nativeLineFunctor.obj X).obj) :=
  (KMap_kZeroObjectClass (nativeFirstSummand_exact X) _).trans
    ((perfectWaldhausen _).kZeroObjectClass_iso (nativeFirstRankOneIso X))

/-- The unchanged original second K-map sends rank one to the native O(-1) class. -/
theorem nativeSecondRankOne_class (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    KMap (nativeSecondSummand_exact X) 0 ((perfectWaldhausen X.obj).kZeroObjectClass
      (rankOnePerfect X.obj)) =
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
        (nativeTautologicalPerfect X) :=
  (KMap_kZeroObjectClass (nativeSecondSummand_exact X) _).trans
    ((perfectWaldhausen _).kZeroObjectClass_iso (nativeSecondRankOneIso X))

/-- Original Phi order gives structure class times inverse negative-line class. -/
theorem nativePhi_rankOne_difference (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    nativeTwoSummandKMap X 0
      ((perfectWaldhausen X.obj).kZeroObjectClass (rankOnePerfect X.obj),
        ((perfectWaldhausen X.obj).kZeroObjectClass (rankOnePerfect X.obj))⁻¹) =
      (perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
          (rankOnePerfect (nativeLineFunctor.obj X).obj) *
        ((perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
          (nativeTautologicalPerfect X))⁻¹ := by
  rw [nativeTwoSummandKMap_apply, map_inv, nativeFirstRankOne_class, nativeSecondRankOne_class]

/-- Every actual arrow O(-1) to O has the original Phi rank-one difference as its signed cone class.
No cofibration hypothesis is imposed on the given arrow. -/
theorem nativeTautologicalArrow_cone_class (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u})
    (f : nativeTautologicalPerfect X ⟶ rankOnePerfect (nativeLineFunctor.obj X).obj) :
    (perfectWaldhausen (nativeLineFunctor.obj X).obj).kZeroObjectClass
      ⟨CochainComplex.mappingCone f.hom,
        locallyPerfect_mappingCone (nativeTautologicalPerfect X).property
          (rankOnePerfect _).property f.hom⟩ =
      nativeTwoSummandKMap X 0
        ((perfectWaldhausen X.obj).kZeroObjectClass (rankOnePerfect X.obj),
          ((perfectWaldhausen X.obj).kZeroObjectClass (rankOnePerfect X.obj))⁻¹) := by
  rw [nativePhi_rankOne_difference]
  exact SplitFactorization.subcategoryCone_kZeroObjectClass (locallyPerfect _)
    (fun hK hL g => locallyPerfect_mappingCone hK hL g) f

end Quillen.PerfectComplexes.ProjectiveLine
