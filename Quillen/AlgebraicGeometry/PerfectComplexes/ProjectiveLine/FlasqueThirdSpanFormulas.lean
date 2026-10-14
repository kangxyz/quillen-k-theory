/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueThirdSpan

/-! # Retained original lower bounds and chain maps of the third endpoint span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint

/-- The explicit original cochain factors retain any specified input lower bound. -/
lemma centerExplicitRaw_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((centerExplicitRaw R).obj K).IsStrictlyGE a := by
  let C := (godementTotal (twoChartLine R)).obj ((rightQRaw R).obj K)
  let : C.IsStrictlyGE a := rightQTotal_isStrictlyGE R K a
  let J := ((Scheme.Modules.pushforward (relativeDiagonal R)).mapHomologicalComplex (.up ℤ)).obj C
  let : CochainComplex.IsStrictlyGE J a := inferInstance
  let : ((godementTotal (relativeSquare R)).obj J).IsStrictlyGE a :=
    godementTotal_isStrictlyGE J a
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE J a i hi)
  change CochainComplex.IsStrictlyGE
    (((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).obj
      ((godementTotal (relativeSquare R)).obj J)) a
  infer_instance

/-- The literal original common model retains every specified input lower bound. -/
lemma center_isStrictlyGE (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (a : ℤ) [K.obj.IsStrictlyGE a] :
    ((center R).obj K).obj.IsStrictlyGE a := by
  let : ((centerExplicitRaw R).obj K).IsStrictlyGE a := centerExplicitRaw_isStrictlyGE R K a
  exact CochainComplex.isStrictlyGE_of_iso ((centerRawUnderlyingIso R).app K).symm a

/-- The first model chain map retains the producer's original proof-forgetting map. -/
lemma thirdToCenter_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((thirdToCenter R).app K).hom =
      ((FlasqueDiagonal.EPlusIso R .third).hom.app K).hom ≫
        ((thirdToCenterPlus R).app K).hom := rfl

/-- The second model chain map is the actual original Plus weak arrow. -/
lemma totalToCenter_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((totalToCenter R).app K).hom = ((totalToCenterPlus R).app K).hom := rfl

/-- The prescribed second Plus arrow uses exactly the original section inverse and actual unit. -/
lemma totalToCenterPlus_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (totalToCenterPlus R).app K =
      (sectionComplexPlusIso (relativeDiagonal R) (relativeSecond R)
        (relativeDiagonal_second R)).inv.app ((sourceTotalPlus R).obj K) ≫
      (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus.map
        ((godementTotalPlusUnit (relativeSquare R)).app (centerInputPlus R K)) := rfl

/-- The first Plus arrow retains the original third coefficient iso and section augmentation. -/
lemma thirdToCenterPlus_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (thirdToCenterPlus R).app K =
      (thirdSectionPlusIso R).hom.app K ≫
        (sectionTotalToRepeated (relativeDiagonal R) (relativeSecond R)).app
          ((rightQPlus R).obj K) := rfl

/-- The actual common model preserves each original zero object. -/
lemma center_isZero (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) (hK : IsZero K) :
    IsZero ((center R).obj K) := (center_exact R).zero hK

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint
