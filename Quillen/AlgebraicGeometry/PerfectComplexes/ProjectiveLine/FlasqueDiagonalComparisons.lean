/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Carriers


public import Quillen.Aglib.CategoryTheory.Functor.UnderlyingIso


public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalSequence

/-! # Actual original diagonal model data and canonical natural endpoint comparisons -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance comparisonStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

section
attribute [local irreducible] godementTotal

/-- The whole original complex equality retains its original total differential and zero terms. -/
lemma E_obj (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((E R v).obj K).obj =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).obj
        ((godementTotal (relativeSquare R)).obj
          (((coefficient R v).mapHomologicalComplex (.up ℤ)).obj K.obj)) := rfl

/-- The whole original chain map uses exactly the first pullback/tensor, total and second image. -/
lemma E_map (R : CommRingCat.{u}) (v : Vertex)
    {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (f : K ⟶ L) :
    ((E R v).map f).hom =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map
          (((coefficient R v).mapHomologicalComplex (.up ℤ)).map f.hom)) := rfl

/-- The original incidence chain map is retained literally in the actual flasque model. -/
lemma incidence_original (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((incidence R).app K).hom =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map
          (((diagonalCoefficientMap R (diagonalIncidence R)).mapCochainComplexPlus.app
            ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)).hom)) := rfl

/-- The original adjoint quotient chain map is retained literally in the actual model. -/
lemma quotient_original (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((quotient R).app K).hom =
      ((Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)).map
        ((godementTotal (relativeSquare R)).map
          (((diagonalCoefficientMap R (diagonalQuotientMap R)).mapCochainComplexPlus.app
            ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)).hom)) := rfl

end

/-- The output underlying comparison uses the original three termwise/total forgetful factors. -/
def rawPlusUnderlyingIso (R : CommRingCat.{u}) (v : Vertex) :
    rawPlus R v ⋙ CochainComplex.Plus.ι (twoChartLine R).Modules ≅ raw R v := by
  let A := FlasqueCoefficients.toPlus (twoChartLine R)
  let B := (coefficient R v).mapCochainComplexPlus
  let C := godementTotalPlus (relativeSquare R)
  let D := (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlus
  let I := CochainComplex.Plus.ι (twoChartLine R).Modules
  let J := CochainComplex.Plus.ι (relativeSquare R).Modules
  let T := godementTotal (relativeSquare R)
  let P := (Scheme.Modules.pushforward (relativeSecond R)).mapHomologicalComplex (.up ℤ)
  let F := (coefficient R v).mapHomologicalComplex (.up ℤ)
  let eD : D ⋙ I ≅ J ⋙ P :=
    (Scheme.Modules.pushforward (relativeSecond R)).mapCochainComplexPlusCompι
  let eC : (C ⋙ D) ⋙ I ≅ J ⋙ T ⋙ P :=
    Functor.associator C D I ≪≫ Functor.isoWhiskerLeft C eD ≪≫
      (Functor.associator C J P).symm ≪≫
      Functor.isoWhiskerRight (AlgebraicGeometry.Scheme.Modules.Godement.totalPlusCompιIso
        (relativeSquare R)) P ≪≫
      Functor.associator J T P
  let eB : (B ⋙ C ⋙ D) ⋙ I ≅ CochainComplex.Plus.ι (twoChartLine R).Modules ⋙ F ⋙ T ⋙ P :=
    Functor.associator B (C ⋙ D) I ≪≫ Functor.isoWhiskerLeft B eC ≪≫
      (Functor.associator B J (T ⋙ P)).symm ≪≫
      Functor.isoWhiskerRight (coefficient R v).mapCochainComplexPlusCompι (T ⋙ P) ≪≫
      Functor.associator (CochainComplex.Plus.ι (twoChartLine R).Modules) F (T ⋙ P)
  exact Functor.associator A (B ⋙ C ⋙ D) I ≪≫ Functor.isoWhiskerLeft A eB ≪≫
    (Functor.associator A (CochainComplex.Plus.ι (twoChartLine R).Modules) (F ⋙ T ⋙ P)).symm ≪≫
    Functor.isoWhiskerRight (toPlusUnderlyingIso (twoChartLine R)) (F ⋙ T ⋙ P)

/-- Forgetting only output proofs retains each original D+ complex naturally and choice-free. -/
def EPlusIso (R : CommRingCat.{u}) (v : Vertex) :
    E R v ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ≅ rawPlus R v :=
  Functor.fullyFaithfulCancelRight (CochainComplex.Plus.ι (twoChartLine R).Modules)
    (Functor.associator (E R v) (FlasqueCoefficients.toPlus (twoChartLine R))
        (CochainComplex.Plus.ι (twoChartLine R).Modules) ≪≫
      Functor.isoWhiskerLeft (E R v) (toPlusUnderlyingIso (twoChartLine R)) ≪≫
      eqToIso (E_underlying R v) ≪≫ (rawPlusUnderlyingIso R v).symm)

/-- Actual model values compute the original derived second image through its installed unit. -/
def EDerivedIso (R : CommRingCat.{u}) (v : Vertex) :
    E R v ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ≅
      FlasqueCoefficients.toPlus (twoChartLine R) ⋙ (coefficient R v).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus (relativeSecond R) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EPlusIso R v) DerivedCategory.Plus.Q ≪≫ rawDerivedIso R v

/-- Original first model endpoint, naturally on all original source chain maps. -/
def EFirstEndpointIso (R : CommRingCat.{u}) :
    E R .first ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ≅
      toOriginalPerfectPlus R ⋙ originalPerfectPlusInclusion R ⋙
        diagonalPerfectGenerationFirstFunctor R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EPlusIso R .first) DerivedCategory.Plus.Q ≪≫ firstEndpointIso R

/-- Original second model endpoint, naturally on all original source chain maps. -/
def ESecondEndpointIso (R : CommRingCat.{u}) :
    E R .second ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ≅
      toOriginalPerfectPlus R ⋙ originalPerfectPlusInclusion R ⋙
        diagonalPerfectGenerationSecondFunctor R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EPlusIso R .second) DerivedCategory.Plus.Q ≪≫ secondEndpointIso R

/-- Original right-Q third endpoint, with the accepted closed projection and section data. -/
def EThirdEndpointIso (R : CommRingCat.{u}) :
    E R .third ⋙ FlasqueCoefficients.toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ≅
      FlasqueCoefficients.toPlus (twoChartLine R) ⋙ DerivedCategory.Plus.Q ⋙
        (moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).rightDerivedFunctorPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (EPlusIso R .third) DerivedCategory.Plus.Q ≪≫ thirdEndpointIso R

/-- The derived comparison component is the installed unit and original total augmentation. -/
lemma EDerivedIso_hom_app (R : CommRingCat.{u}) (v : Vertex)
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (EDerivedIso R v).hom.app K =
      DerivedCategory.Plus.Q.map ((EPlusIso R v).hom.app K) ≫
      (derivedPushforwardPlusUnit (relativeSecond R)).app
        ((godementTotalPlus (relativeSquare R)).obj
          ((coefficient R v).mapCochainComplexPlus.obj
            ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K))) ≫
      (asIso (godementTotalDerivedAugmentation (relativeSecond R))).inv.app
        ((coefficient R v).mapCochainComplexPlus.obj
          ((FlasqueCoefficients.toPlus (twoChartLine R)).obj K)) := by
  simp only [EDerivedIso, rawDerivedIso, rawPlus, godementTotalDerivedPushforwardIso,
    godementTotalDerivedUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    asIso_hom, Category.id_comp]

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
