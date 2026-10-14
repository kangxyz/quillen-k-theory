/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueGammaRightWeakPrecomposition

/-! # Actual Gamma-third identity through the original right-pair contraction and model units -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
open FlasqueTensorAdditivity

/-- A natural transformation carrying its objectwise weak law at the symbolic model boundary. -/
def liftPlusModelWeakNatTrans {C : Type*} [Category C] (X : Scheme.{u})
    {F G : C ⥤ FlasqueBoundedBelow.Obj X} {A B : C ⥤ CochainComplex.Plus X.Modules}
    (eF : F ⋙ (FlasqueBoundedBelow.objects X).ι ≅ A ⋙ CochainComplex.Plus.ι X.Modules)
    (eG : G ⋙ (FlasqueBoundedBelow.objects X).ι ≅ B ⋙ CochainComplex.Plus.ι X.Modules)
    (a : A ⟶ B) (ha : ∀ K, QuasiIso (a.app K).hom) :
    { b : F ⟶ G // ∀ K, (FlasqueBoundedBelow.waldhausen X).weq (b.app K) } :=
  ⟨liftPlusModelNatTrans X eF eG a, liftPlusModelNatTrans_weak X eF eG a ha⟩

/-- Actual original totalization of the original flasque input, with its actual model proof. -/
def modelTotal (R : CommRingCat.{u}) :=
  FlasqueBoundedBelow.inclusion (twoChartLine R) ⋙ FlasqueBoundedBelow.total (twoChartLine R)

/-- Actual model total to its original underlying cochain carrier. -/
def modelTotalRawCarrierIso (R : CommRingCat.{u}) :
    modelTotal R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙ godementTotal (twoChartLine R) := by
  let P := twoChartLine R
  let A := FlasqueBoundedBelow.inclusion P
  let T := FlasqueBoundedBelow.total P
  let B := (BoundedBelow.objects P).ι
  let I := (FlasqueBoundedBelow.objects P).ι
  let V := godementTotal P
  exact Functor.associator A T I ≪≫ Functor.isoWhiskerLeft A (totalCarrierIso P) ≪≫
    (Functor.associator A B V).symm ≪≫ Functor.isoWhiskerRight (inclusionCarrierIso P) V

/-- The same original total through canonical model and Plus proof-forgetting comparisons. -/
def modelTotalUnderlyingIso (R : CommRingCat.{u}) :
    modelTotal R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (FlasqueCoefficients.toPlus (twoChartLine R) ⋙ godementTotalPlus (twoChartLine R)) ⋙
        CochainComplex.Plus.ι (twoChartLine R).Modules :=
  modelTotalRawCarrierIso R ≪≫
    (plusTotalCarrierIso (twoChartLine R) (FlasqueCoefficients.toPlus (twoChartLine R))
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι
      (FlasqueDiagonal.toPlusUnderlyingIso (twoChartLine R))).symm

/-- The actual right-Q bounded model before applying either chosen total. -/
def rightQCarrierIso (R : CommRingCat.{u}) :
    FlasqueThirdEndpoint.rightQ R ⋙ (BoundedBelow.objects (twoChartLine R)).ι ≅
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⋙
        (moduleTensorRightFunctor (twoChartLine R)
          (tautologicalQuotientLine R)).mapHomologicalComplex (.up ℤ) := by
  unfold FlasqueThirdEndpoint.rightQ FlasqueThirdEndpoint.rightQRaw
  exact ObjectProperty.liftCompιIso _ _ _

/-- Canonical original carrier comparisons align the literal right resolved pair and actual Gamma.
-/
def rightQTotalGammaUnderlyingIso (R : CommRingCat.{u}) :
    rightQTotalGamma R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ≅
      (FlasqueCoefficients.toPlus (twoChartLine R) ⋙ originalRightLineGodementResolved R) ⋙
        CochainComplex.Plus.ι (twoChartLine R).Modules :=
  actualResolvedCarrierIso R (FlasqueThirdEndpoint.rightQ R)
    (FlasqueBoundedBelow.objects (twoChartLine R)).ι
    ((moduleTensorRightFunctor (twoChartLine R)
      (tautologicalQuotientLine R)).mapHomologicalComplex (.up ℤ)) (rightQCarrierIso R) ≪≫
    (precomposedResolvedCarrierIso (twoChartLine R)
      (FlasqueCoefficients.toPlus (twoChartLine R))
      (FlasqueBoundedBelow.objects (twoChartLine R)).ι
      (FlasqueDiagonal.toPlusUnderlyingIso (twoChartLine R))
      (moduleTensorRightFunctor (twoChartLine R) (tautologicalQuotientLine R))
      (tautologicalLine R)).symm

/-- Actual original cochain contraction, with the named canonical carrier comparisons retained. -/
def rightQGammaUnderlying (R : CommRingCat.{u}) :
    modelTotal R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι ⟶
      rightQTotalGamma R ⋙ (FlasqueBoundedBelow.objects (twoChartLine R)).ι :=
  (modelTotalUnderlyingIso R).hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (FlasqueCoefficients.toPlus (twoChartLine R))
      (originalRightLineGodementContractionMap R))
      (CochainComplex.Plus.ι (twoChartLine R).Modules) ≫
    (rightQTotalGammaUnderlyingIso R).inv

/-- The literal original contraction with its weak law bundled before model specialization. -/
def rightQGammaWeakContraction (R : CommRingCat.{u}) :
    { b : modelTotal R ⟶ rightQTotalGamma R //
      ∀ K, (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (b.app K) } :=
  liftPlusModelWeakNatTrans (twoChartLine R) (modelTotalUnderlyingIso R)
    (rightQTotalGammaUnderlyingIso R)
    (Functor.whiskerLeft (FlasqueCoefficients.toPlus (twoChartLine R))
      (originalRightLineGodementContractionMap R))
    (rightContraction_precompose_weak R (FlasqueCoefficients.toPlus (twoChartLine R)))

/-- Lift the original determinant/associator/unitor/braiding map and unit to the chosen model. -/
def rightQGammaContraction (R : CommRingCat.{u}) : modelTotal R ⟶ rightQTotalGamma R :=
  (rightQGammaWeakContraction R).val

lemma rightQGammaContraction_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((rightQGammaContraction R).app K).hom =
      (rightQGammaUnderlying R).app K := rfl

/-- Both named carrier maps are actual chain isos; the middle map is the original weak contraction.
-/
lemma rightQGammaContraction_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((rightQGammaContraction R).app K) :=
  (rightQGammaWeakContraction R).property K

lemma modelTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (modelTotal R) :=
  (FlasqueBoundedBelow.inclusion_exact (twoChartLine R)).comp
    (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- The actual lifted contraction compares the original chosen-zero K-maps in every degree. -/
lemma rightQTotalGamma_KMap_eq_total (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (rightQTotalGamma_exact R) n =
      Waldhausen.KMap (modelTotal_exact R) n :=
  (Waldhausen.KMap_eq_of_weakNatTrans (modelTotal_exact R) (rightQTotalGamma_exact R)
    (rightQGammaContraction R) (rightQGammaContraction_weak R) n).symm

/-- The original forward flasque unit gives the actual identity K-map in every degree. -/
lemma modelTotal_KMap_eq_id (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (modelTotal_exact R) n = MonoidHom.id _ := by
  have h := Waldhausen.KMap_eq_of_weakNatTrans
    (Waldhausen.IsExact.id (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq)
    (modelTotal_exact R) (FlasqueBoundedBelow.flasqueUnit (twoChartLine R))
    (FlasqueBoundedBelow.flasqueUnit_weak (twoChartLine R)) n
  exact h.symm.trans (Waldhausen.KMap_id _ n)

/-- Actual Gamma of the original third diagonal vertex induces identity on native K, including K0.
-/
theorem gammaThird_KMap_eq_id (R : CommRingCat.{u}) (n : ℕ) :
    tensorVertexKMap R .third n = MonoidHom.id _ :=
  (gammaThird_KMap_eq_rightQTotal R n).trans
    ((rightQTotalGamma_KMap_eq_total R n).trans (modelTotal_KMap_eq_id R n))

theorem gammaThird_KMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    tensorVertexKMap R .third n x = x :=
  DFunLike.congr_fun (gammaThird_KMap_eq_id R n) x

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
