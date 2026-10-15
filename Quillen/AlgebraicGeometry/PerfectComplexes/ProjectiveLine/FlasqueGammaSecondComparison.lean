/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Carrier
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaCarrierComparisons
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaSecondSpan
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePositiveSourceAssociation

/-! # Actual Gamma-second positivity through the original left-pair contraction -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
open FlasqueTensorAdditivity

/-- The exact actual left-Q bounded functor followed by its actual total and Gamma. -/
def leftQTotalGamma (R : CommRingCat.{u}) :=
  (SecondEndpoint.quotientLeftBounded R ⋙ FlasqueBoundedBelow.total (twoChartLine R)) ⋙ Gamma R

/-- The natural identification of the underlying quotient-line twist with left tensor by the
tautological quotient line.
-/
def quotientLeftCarrierIso (R : CommRingCat.{u}) :
    SecondEndpoint.quotientLeftBounded R ⋙ (BoundedBelow.objects (twoChartLine R)).ι ≅
      (BoundedBelow.objects (twoChartLine R)).ι ⋙
        AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalQuotientLine R) := by
  unfold SecondEndpoint.quotientLeftBounded
  exact ObjectProperty.liftCompιIso _ _ _

/-- The actual chosen bounded total, before any original contraction is applied. -/
def boundedTotalUnderlyingIso (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.total (twoChartLine R) ⋙
        (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (boundedToPlus (twoChartLine R) ⋙ godementTotalPlus (twoChartLine R)) ⋙
        CochainComplex.Plus.ι (twoChartLine R).Modules :=
  totalCarrierIso (twoChartLine R) ≪≫
    (AlgebraicGeometry.Scheme.Modules.Godement.compTotalPlusCarrierIso (twoChartLine R)
      (boundedToPlus (twoChartLine R))
      (BoundedBelow.objects (twoChartLine R)).ι (boundedToPlusCarrierIso (twoChartLine R))).symm

/-- The actual Gamma-left-Q target aligned through the original proof-forgetting carriers. -/
def leftQTotalGammaUnderlyingIso (R : CommRingCat.{u}) :
    leftQTotalGamma R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (boundedToPlus (twoChartLine R) ⋙ originalLeftLineGodementResolved R) ⋙
        CochainComplex.Plus.ι (twoChartLine R).Modules :=
  actualResolvedCarrierIso R (SecondEndpoint.quotientLeftBounded R)
    (BoundedBelow.objects (twoChartLine R)).ι
    (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalQuotientLine R))
      (quotientLeftCarrierIso R) ≪≫
    (AlgebraicGeometry.Scheme.Modules.Godement.precompResolvedContractionCompιIso (twoChartLine R)
      (boundedToPlus (twoChartLine R))
      (BoundedBelow.objects (twoChartLine R)).ι (boundedToPlusCarrierIso (twoChartLine R))
      (moduleTensorLeftFunctor (twoChartLine R) (tautologicalQuotientLine R))
      (tautologicalLine R)).symm

/-- Original determinant/associator/unitor contraction and inner unit, lifted to the actual model.
-/
def leftQGammaContractionBounded (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.total (twoChartLine R) ⟶ leftQTotalGamma R :=
  liftPlusModelNatTrans (twoChartLine R) (boundedTotalUnderlyingIso R)
    (leftQTotalGammaUnderlyingIso R)
    (whiskerLeft (boundedToPlus (twoChartLine R)) (originalLeftLineGodementContractionMap R))

lemma leftQGammaContractionBounded_weak (R : CommRingCat.{u})
    (K : BoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((leftQGammaContractionBounded R).app K) :=
  liftPlusModelNatTrans_weak (twoChartLine R) (boundedTotalUnderlyingIso R)
    (leftQTotalGammaUnderlyingIso R)
    (whiskerLeft (boundedToPlus (twoChartLine R)) (originalLeftLineGodementContractionMap R))
    (fun K => originalLeftLineGodementContractionMap_quasiIso R
      ((boundedToPlus (twoChartLine R)).obj K)) K

/-- Original source association for the actual second source, with no model choice. -/
def selfLeftQGammaAssociation (R : CommRingCat.{u}) :
    SelfBaseChange.source R ⋙ leftQTotalGamma R ≅ secondGammaSource R :=
  (associator (SelfBaseChange.source R)
    (SecondEndpoint.quotientLeftBounded R ⋙ FlasqueBoundedBelow.total (twoChartLine R))
    (Gamma R)).symm ≪≫
    isoWhiskerRight ((associator (SelfBaseChange.source R)
      (SecondEndpoint.quotientLeftBounded R) (FlasqueBoundedBelow.total (twoChartLine R))).symm)
      (Gamma R)

/-- The actual original source total maps to actual Gamma of the actual original second source. -/
def secondGammaContraction (R : CommRingCat.{u}) :
    SelfBaseChange.spanLeft R ⟶ secondGammaSource R :=
  whiskerLeft (SelfBaseChange.source R) (leftQGammaContractionBounded R) ≫
    (selfLeftQGammaAssociation R).hom

lemma secondGammaContraction_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((secondGammaContraction R).app K) :=
  (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    (leftQGammaContractionBounded_weak R ((SelfBaseChange.source R).obj K))
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)

/-- Actual Gamma of the original second diagonal vertex is the actual positive column K-map. -/
theorem gammaSecond_KMap_eq_positive (R : CommRingCat.{u}) (n : ℕ) :
    tensorVertexKMap R .second n =
      Waldhausen.KMap ((FlasqueCoefficients.G0_exact R).comp
        (FlasquePhiColumns.positive_exact R)) n :=
  (gammaSecond_KMap_eq_source R n).trans
    ((Waldhausen.KMap_eq_of_weakNatTrans (SelfBaseChange.spanLeft_exact R)
      (secondGammaSource_exact R) (secondGammaContraction R)
      (secondGammaContraction_weak R) n).symm.trans (sourcePositive_KMap R n))

theorem gammaSecond_KMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    tensorVertexKMap R .second n x =
      Waldhausen.KMap ((FlasqueCoefficients.G0_exact R).comp
        (FlasquePhiColumns.positive_exact R)) n x :=
  DFunLike.congr_fun (gammaSecond_KMap_eq_positive R n) x

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
