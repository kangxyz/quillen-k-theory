/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SecondEndpointModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SelfBaseChangeSpan

/-! # Canonical original alpha-target and projection-formula source alignment -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
variable (R : CommRingCat.{u})

/-- Only original proof-forgetting comparisons and canonical associators are used. -/
def UUnderlyingIso : UPlus R ⋙ CochainComplex.Plus.ι (twoChartLine R).Modules ≅
    SelfBaseChange.targetRaw R := by
  let B := (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus
  let I := CochainComplex.Plus.ι (twoChartLine R).Modules
  let J := CochainComplex.Plus.ι (relativeSquare R).Modules
  let P := (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)
  let F := (Scheme.Modules.pullback (relativeFirst R)).mapHomologicalComplex (.up ℤ)
  let T := godementTotal (relativeSquare R)
  let A := (FlasqueBoundedBelow.objects (twoChartLine R)).ι
  exact associator (CPlus R) B I ≪≫
    isoWhiskerLeft (CPlus R)
      (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlusCompι ≪≫
    (associator (CPlus R) J P).symm ≪≫ isoWhiskerRight (CUnderlyingIso R) P ≪≫
    associator A (F ⋙ T) P ≪≫ isoWhiskerLeft A (associator F T P)

/-- The literal beta source forgets to original left Q tensor of alpha's actual target. -/
def tensorUUnderlyingIso : tensorUPlus R ⋙ CochainComplex.Plus.ι (twoChartLine R).Modules ≅
    tensorURaw R := by
  let T := moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R)
  let I := CochainComplex.Plus.ι (twoChartLine R).Modules
  exact associator (UPlus R) T.mapCochainComplexPlus I ≪≫
    isoWhiskerLeft (UPlus R) T.mapCochainComplexPlusCompι ≪≫
    (associator (UPlus R) I (T.mapHomologicalComplex (.up ℤ))).symm ≪≫
    isoWhiskerRight (UUnderlyingIso R) (T.mapHomologicalComplex (.up ℤ))

/-- The original beta on native complexes, preceded only by the canonical source comparison. -/
def betaRaw : tensorURaw R ⟶ VRaw R :=
  (tensorUUnderlyingIso R).inv ≫
    whiskerRight (beta R) (CochainComplex.Plus.ι (twoChartLine R).Modules)

lemma betaRaw_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (betaRaw R).app K = (tensorUUnderlyingIso R).inv.app K ≫ ((beta R).app K).hom := rfl

lemma betaRaw_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (a : K ⟶ L) :
    (tensorURaw R).map a ≫ (betaRaw R).app L =
      (betaRaw R).app K ≫ (VRaw R).map a := (betaRaw R).naturality a

lemma betaRaw_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((betaRaw R).app K) := by
  let e := (tensorUUnderlyingIso R).inv.app K
  let : QuasiIso e := inferInstance
  let : QuasiIso ((beta R).app K).hom := beta_quasiIso R K
  change QuasiIso (e ≫ ((beta R).app K).hom)
  infer_instance

end Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
