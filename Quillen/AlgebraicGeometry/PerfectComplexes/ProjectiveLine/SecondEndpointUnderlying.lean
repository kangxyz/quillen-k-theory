/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.PlusAdditive


public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SecondEndpointResolution
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalComparisons

/-! # Original underlying-complex comparisons for second endpoint model values -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
open FlasqueCoefficients

instance CRaw_additive (R : CommRingCat.{u}) : (CRaw R).Additive := by
  unfold CRaw CPlus firstPlus
  infer_instance

instance VRaw_additive (R : CommRingCat.{u}) : (VRaw R).Additive := by
  unfold VRaw VPlus CPlus firstPlus squareTensor
  infer_instance

variable (R : CommRingCat.{u})

/-- The original first pullback and total in the plain complex carrier. -/
def CNative : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex
    (relativeSquare R).Modules ℤ :=
  (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
    (Scheme.Modules.pullback (relativeFirst R)).mapHomologicalComplex (.up ℤ) ⋙
      godementTotal (relativeSquare R)

instance CNative_additive : (CNative R).Additive := by
  unfold CNative
  infer_instance

/-- The original V expression in the plain complex carrier. -/
def VNative : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤ CochainComplex
    (twoChartLine R).Modules ℤ :=
  CRaw R ⋙ (squareTensor R).mapHomologicalComplex (.up ℤ) ⋙
    godementTotal (relativeSquare R) ⋙
      (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)

instance VNative_additive : (VNative R).Additive := by
  unfold VNative
  infer_instance

/-- Forgetting only the lower-bound witnesses retains the original first pullback and total. -/
def CUnderlyingIso : CRaw R ≅ CNative R := by
  let A := toPlus (twoChartLine R)
  let B := (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus
  let I := CochainComplex.Plus.ι (relativeSquare R).Modules
  let J := CochainComplex.Plus.ι (twoChartLine R).Modules
  let P := (Scheme.Modules.pullback (relativeFirst R)).mapHomologicalComplex (.up ℤ)
  let T := godementTotal (relativeSquare R)
  exact associator (firstPlus R) (godementTotalPlus (relativeSquare R)) I ≪≫
    isoWhiskerLeft (firstPlus R) (AlgebraicGeometry.Scheme.Modules.Godement.totalPlusCompιIso
      (relativeSquare R)) ≪≫
    (associator (firstPlus R) I T).symm ≪≫
    isoWhiskerRight (associator A B I ≪≫
      isoWhiskerLeft A (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlusCompι ≪≫
      (associator A J P).symm ≪≫
      isoWhiskerRight (FlasqueDiagonal.toPlusUnderlyingIso (twoChartLine R)) P) T ≪≫
    associator (FlasqueBoundedBelow.objects (twoChartLine R)).ι P T

/-- The original line/total/image forgetful factors retain every original V chain map. -/
def VUnderlyingIso : VRaw R ≅ VNative R := by
  let A := CPlus R
  let B := (squareTensor R).mapCochainComplexPlus
  let C := godementTotalPlus (relativeSquare R)
  let D := (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus
  let I := CochainComplex.Plus.ι (twoChartLine R).Modules
  let J := CochainComplex.Plus.ι (relativeSquare R).Modules
  let T := godementTotal (relativeSquare R)
  let P := (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)
  let F := (squareTensor R).mapHomologicalComplex (.up ℤ)
  let eD : D ⋙ I ≅ J ⋙ P :=
    (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlusCompι
  let eC : (C ⋙ D) ⋙ I ≅ J ⋙ T ⋙ P :=
    associator C D I ≪≫ isoWhiskerLeft C eD ≪≫
      (associator C J P).symm ≪≫
      isoWhiskerRight (AlgebraicGeometry.Scheme.Modules.Godement.totalPlusCompιIso (relativeSquare
        R)) P ≪≫
      associator J T P
  let eB : (B ⋙ C ⋙ D) ⋙ I ≅ J ⋙ F ⋙ T ⋙ P :=
    associator B (C ⋙ D) I ≪≫ isoWhiskerLeft B eC ≪≫
      (associator B J (T ⋙ P)).symm ≪≫
      isoWhiskerRight (squareTensor R).mapCochainComplexPlusCompι (T ⋙ P) ≪≫
      associator J F (T ⋙ P)
  exact associator A (B ⋙ C ⋙ D) I ≪≫ isoWhiskerLeft A eB ≪≫
    (associator A J (F ⋙ T ⋙ P)).symm

/-- The raw original right weak leg, through the canonical original proof-forgetful comparison. -/
def rightRawMap : FlasqueDiagonal.raw R .second ⟶ VRaw R :=
  (FlasqueDiagonal.rawPlusUnderlyingIso R .second).inv ≫
    whiskerRight (rightPlusMap R) (CochainComplex.Plus.ι (twoChartLine R).Modules)

lemma rightRawMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((rightRawMap R).app K) := by
  let e := (FlasqueDiagonal.rawPlusUnderlyingIso R .second).inv.app K
  let : QuasiIso e := inferInstance
  let : QuasiIso ((rightPlusMap R).app K).hom := rightPlusMap_quasiIso R K
  change QuasiIso (e ≫ ((rightPlusMap R).app K).hom)
  infer_instance

end Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
