/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePhiOffDiagonal
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.EulerInverse

/-!
# Original second diagonal through the actual Euler endpoint normalization

Forward base and line augmentations compare the actual injected Phi/G1 with
the actual shifted Euler square endpoint. Original right-tensor symmetry,
two-line associator, signed shift, and the E0 left unitor are retained.
-/
@[expose] public section

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
open Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction


open CategoryTheory.ExactCategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
open StrictPositiveRetraction FlasqueTwoSummands FlasqueCoefficients

/-- Literal right tensor on the original bounded-below perfect category. -/
def boundedRightTensor (R : CommRingCat.{u}) :
    BoundedBelow.Obj (twoChartLine R) ⥤ BoundedBelow.Obj (twoChartLine R) :=
  ObjectProperty.lift _ ((BoundedBelow.objects (twoChartLine R)).ι ⋙
    AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)) (fun K => by
      obtain ⟨hp, a, ha⟩ := K.property
      let := ha
      exact ⟨rightTensor_locallyPerfect R hp, a, rightTensor_isStrictlyGE R K.obj a⟩)

instance boundedRightTensor_additive (R : CommRingCat.{u}) :
    (boundedRightTensor R).Additive := by
  unfold boundedRightTensor
  infer_instance

/-- Right tensor by the tautological line on bounded-below perfect complexes, bundled with
preservation of degreewise short exact sequences.
-/
def boundedRightTensorExactFunctor (R : CommRingCat.{u}) : ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R)))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex (twoChartLine R)))
      (BoundedBelow.objects (twoChartLine R))) where
  toFunctor := boundedRightTensor R
  map_conflation S hs := by
    change (S.map (BoundedBelow.objects (twoChartLine R)).ι).ShortExact at hs
    change ((S.map (BoundedBelow.objects (twoChartLine R)).ι).map
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R))).ShortExact
    exact hs.map_of_exact _

lemma boundedRightTensor_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (boundedRightTensor R) where
  zero h := (boundedRightTensor R).map_isZero h
  cofibration f hf := (boundedRightTensorExactFunctor R).map_inflation f hf
  weak f hf := by
    change QuasiIso f.hom at hf
    let := hf
    exact AlgebraicGeometry.Scheme.Modules.Complex.tensorRight_quasiIso (tautologicalLine R) f.hom
  pushout hi h := (boundedRightTensorExactFunctor R).map_isPushout hi h

/-- Identity chain maps reconcile only the two proofs of right-tensor model membership. -/
def rightTensorInclusionIso (R : CommRingCat.{u}) :
    FlasqueBoundedBelow.inclusion (twoChartLine R) ⋙ boundedRightTensor R ≅ rightTensor R :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      (Iso.refl ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).obj
        K.obj))) (by
        intro K L f
        apply ObjectProperty.hom_ext
        change (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).map f.hom
          ≫ 𝟙 _ =
          𝟙 _ ≫ (AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).map
            f.hom
        simp)

/-- Actual negative pullback of the original strict coefficient, before any totalization. -/
def strictNegativeBounded (R : CommRingCat.{u}) :=
  (strictPullback (projection R) ⋙ strictToBoundedBelow (twoChartLine R)) ⋙ boundedNegativeTwist R

lemma strictNegativeBounded_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq (strictNegativeBounded R) :=
  ((strictPullback_waldhausenExact (projection R)).comp
    (strictToBoundedBelow_exact (twoChartLine R))).comp (boundedNegativeTwist_exact R)

/-- The strict negative pullback followed by Godement totalization on the two-chart line. -/
def strictNegativeTotal (R : CommRingCat.{u}) :=
  strictNegativeBounded R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

lemma strictNegativeTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (strictNegativeTotal R) :=
  (strictNegativeBounded_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- Original negative tensor of the pulled forward A-to-T_A augmentation. -/
def strictNegativeUnit (R : CommRingCat.{u}) :
    strictNegativeBounded R ⟶ strictTotal (Spec R) ⋙ second R :=
  Functor.whiskerRight (strictPullbackUnit R) (boundedNegativeTwist R) ≫
    (Functor.associator (strictTotal (Spec R)) (first R) (boundedNegativeTwist R)).hom

lemma strictNegativeUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((strictNegativeUnit R).app K) :=
  (BoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    ((boundedNegativeTwist_exact R).weak _ (strictPullbackUnit_weak R K))
    ((BoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)

/-- The Godement-totalized comparison from the strict negative pullback to the negative column of
the totalized base model.
-/
def strictNegativeTotalUnit (R : CommRingCat.{u}) :
    strictNegativeTotal R ⟶ strictTotal (Spec R) ⋙ secondTotal R :=
  Functor.whiskerRight (strictNegativeUnit R) (FlasqueBoundedBelow.total (twoChartLine R)) ≫
    (Functor.associator (strictTotal (Spec R)) (second R)
      (FlasqueBoundedBelow.total (twoChartLine R))).hom

lemma strictNegativeTotalUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((strictNegativeTotalUnit R).app K) :=
  (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    (FlasqueBoundedBelow.total_weak ((strictNegativeUnit R).app K) (strictNegativeUnit_weak R K))
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)

/-- The totalized second coproduct inclusion, precomposed with Godement totalization of the strict
base model.
-/
def strictSecondPhiUnit (R : CommRingCat.{u}) :
    strictTotal (Spec R) ⋙ secondTotal R ⟶ strictPhiSecond R :=
  Functor.whiskerLeft (strictTotal (Spec R)) (secondPhiUnit R)

instance strictSecondPhiUnit_isIso (R : CommRingCat.{u}) : IsIso (strictSecondPhiUnit R) := by
  unfold strictSecondPhiUnit
  infer_instance

/-- The actual second matrix diagonal with literal source total precomposition. -/
def G1Second (R : CommRingCat.{u}) := strictPhiSecond R ⋙ G1 R

lemma G1Second_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (G1Second R) :=
  (strictPhiSecond_exact R).comp (G1_exact R)

/-- The comparison to the second `G1` matrix entry, obtained by applying `G1` to the totalized
negative augmentation and second coproduct inclusion.
-/
def negativeToG1Second (R : CommRingCat.{u}) :
    strictNegativeTotal R ⋙ G1 R ⟶ G1Second R :=
  Functor.whiskerRight (strictNegativeTotalUnit R) (G1 R) ≫
    Functor.whiskerRight (strictSecondPhiUnit R) (G1 R)

lemma negativeToG1Second_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq ((negativeToG1Second R).app K) :=
  (FlasqueBoundedBelow.waldhausen (Spec R)).weq.comp_mem _ _
    ((G1_exact R).weak _ (strictNegativeTotalUnit_weak R K))
    ((FlasqueBoundedBelow.waldhausen (Spec R)).weq_iso _ inferInstance)

/-- Original right tensor and native two-line associator, on the original coefficient. -/
def negativeRightTensorIso (R : CommRingCat.{u}) :
    strictNegativeBounded R ⋙ boundedRightTensor R ≅
      Euler.endpointBounded R (Euler.sequence R).X₁ (Euler.squareEndpoint_strictPerfect R) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ ((Euler.originalRightTensorIso R).app K))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (Euler.originalRightTensorIso R).hom.naturality f)

/-- The actual forward line augmentation before right tensor; source remains strict only here. -/
def strictNegativeLineUnit (R : CommRingCat.{u}) :
    strictNegativeBounded R ⟶ strictNegativeTotal R ⋙
      FlasqueBoundedBelow.inclusion (twoChartLine R) :=
  Functor.whiskerLeft (strictNegativeBounded R) (FlasqueBoundedBelow.unit (twoChartLine R))

lemma strictNegativeLineUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((strictNegativeLineUnit R).app K) :=
  FlasqueBoundedBelow.unit_weak _ _

/-- Actual right tensor of the forward line augmentation, reconciled by identity chain maps. -/
def negativeRightUnit (R : CommRingCat.{u}) :
    strictNegativeBounded R ⋙ boundedRightTensor R ⟶ strictNegativeTotal R ⋙ rightTensor R :=
  Functor.whiskerRight (strictNegativeLineUnit R) (boundedRightTensor R) ≫
    (Functor.associator (strictNegativeTotal R) (FlasqueBoundedBelow.inclusion (twoChartLine R))
      (boundedRightTensor R)).hom ≫
        Functor.whiskerLeft (strictNegativeTotal R) (rightTensorInclusionIso R).hom

lemma negativeRightUnit_weak (R : CommRingCat.{u}) (K : StrictPerfect (Spec R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((negativeRightUnit R).app K) :=
  (BoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    ((boundedRightTensor_exact R).weak _ (strictNegativeLineUnit_weak R K))
    ((BoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
      ((BoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)
      ((BoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance))

/-- Actual total, projection and original signed shift after a bounded line coefficient. -/
def projectedShift (R : CommRingCat.{u}) :=
  FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R ⋙ modelShift (Spec R) 1

lemma projectedShift_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (projectedShift R) :=
  (FlasqueBoundedBelow.total_exact (twoChartLine R)).comp
    ((G0_exact R).comp (modelShift_exact (Spec R) 1))

/-- Canonical associators retain exactly the original G1 pipeline. -/
def rightProjectedShiftIso (R : CommRingCat.{u}) :
    rightTensor R ⋙ projectedShift R ≅ G1 R :=
  (Functor.associator (rightTensor R) (FlasqueBoundedBelow.total (twoChartLine R))
    (G0 R ⋙ modelShift (Spec R) 1)).symm

/-- The associativity identification of right tensor followed by shifted projection with `G1`, after
the strict negative total functor.
-/
def negativeRightProjectedIso (R : CommRingCat.{u}) :
    (strictNegativeTotal R ⋙ rightTensor R) ⋙ projectedShift R ≅
      strictNegativeTotal R ⋙ G1 R :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictNegativeTotal R) (rightProjectedShiftIso R)

/-- Canonical associators retain the actual projected Euler E2 and its signed shift. -/
def EulerShiftProjectionIso (R : CommRingCat.{u}) :
    Euler.E2Shift R ≅
      Euler.endpointBounded R (Euler.sequence R).X₁ (Euler.squareEndpoint_strictPerfect R) ⋙
        projectedShift R :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _)

/-- Literal forward weak span from the frozen actual Euler E2[1] to the original G1 wrapper. -/
def EulerShiftRightIso (R : CommRingCat.{u}) :
    Euler.E2Shift R ≅ (strictNegativeBounded R ⋙ boundedRightTensor R) ⋙ projectedShift R :=
  EulerShiftProjectionIso R ≪≫
    Functor.isoWhiskerRight (negativeRightTensorIso R).symm (projectedShift R)

/-- The actual projected right tensor of the original coefficient before line totalization. -/
def rawRightProjected (R : CommRingCat.{u}) :=
  (strictNegativeBounded R ⋙ boundedRightTensor R) ⋙ projectedShift R

lemma rawRightProjected_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (rawRightProjected R) :=
  ((strictNegativeBounded_exact R).comp (boundedRightTensor_exact R)).comp (projectedShift_exact R)

/-- The actual projected right tensor after the forward line total augmentation. -/
def totalRightProjected (R : CommRingCat.{u}) :=
  (strictNegativeTotal R ⋙ rightTensor R) ⋙ projectedShift R

lemma totalRightProjected_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (strictWaldhausen (Spec R)).cof (strictWaldhausen (Spec R)).weq
    (FlasqueBoundedBelow.waldhausen (Spec R)).cof
    (FlasqueBoundedBelow.waldhausen (Spec R)).weq (totalRightProjected R) :=
  ((strictNegativeTotal_exact R).comp (rightTensor_exact R)).comp (projectedShift_exact R)

/-- This original natural weak map is kept separate from its two actual chain isomorphisms. -/
def negativeProjectedUnit (R : CommRingCat.{u}) : rawRightProjected R ⟶ totalRightProjected R :=
  Functor.whiskerRight (negativeRightUnit R) (projectedShift R)

/-- The original weak unit is compared before projection, preserving original KMap composition. -/
lemma totalRightProjected_KMap_eq_raw (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (totalRightProjected_exact R) n =
      Waldhausen.KMap (rawRightProjected_exact R) n := by
  have hraw := (strictNegativeBounded_exact R).comp (boundedRightTensor_exact R)
  have htot := (strictNegativeTotal_exact R).comp (rightTensor_exact R)
  have hw := Waldhausen.KMap_eq_of_weakNatTrans hraw htot
    (negativeRightUnit R) (negativeRightUnit_weak R) n
  calc
    _ = (Waldhausen.KMap (projectedShift_exact R) n).comp (Waldhausen.KMap htot n) :=
      (Waldhausen.KMap_comp_KMap htot (projectedShift_exact R) n).symm
    _ = (Waldhausen.KMap (projectedShift_exact R) n).comp (Waldhausen.KMap hraw n) := by rw [hw]
    _ = _ := Waldhausen.KMap_comp_KMap hraw (projectedShift_exact R) n

/-- The original E0 endpoint left unitor, in the actual bounded perfect model. -/
def EulerUnitBoundedIso (R : CommRingCat.{u}) :
    Euler.endpointBounded R (Euler.sequence R).X₃ (Euler.unitEndpoint_strictPerfect R) ≅
      strictPullback (projection R) ⋙ strictToBoundedBelow (twoChartLine R) :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ ((Euler.unitEndpointIso R).app K))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (Euler.unitEndpointIso R).hom.naturality f)

/-- Actual E0 left unitor followed by actual total and projection. -/
def EulerE0PositiveIso (R : CommRingCat.{u}) : Euler.E0 R ≅ positive R :=
  Functor.isoWhiskerRight (EulerUnitBoundedIso R)
      (FlasqueBoundedBelow.total (twoChartLine R) ⋙ G0 R) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (strictPullback (projection R)) (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm

/-- The actual second diagonal equals the original source total map, all n including zero. -/
theorem G1Second_KMap_eq_strictTotal (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (G1Second_exact R) n = Waldhausen.KMap (strictTotal_exact (Spec R)) n := by
  have hneg := (strictNegativeTotal_exact R).comp (G1_exact R)
  calc
    _ = Waldhausen.KMap hneg n :=
      (Waldhausen.KMap_eq_of_weakNatTrans hneg (G1Second_exact R)
        (negativeToG1Second R) (negativeToG1Second_weak R) n).symm
    _ = Waldhausen.KMap (totalRightProjected_exact R) n :=
      (Waldhausen.KMap_eq_of_iso (totalRightProjected_exact R) hneg
        (negativeRightProjectedIso R) n).symm
    _ = Waldhausen.KMap (rawRightProjected_exact R) n :=
      totalRightProjected_KMap_eq_raw R n
    _ = Waldhausen.KMap (Euler.E2Shift_exact R) n :=
      (Waldhausen.KMap_eq_of_iso (Euler.E2Shift_exact R) (rawRightProjected_exact R)
        (EulerShiftRightIso R) n).symm
    _ = Waldhausen.KMap (Euler.E0_exact R) n := Euler.KMap_E2Shift_eq_E0 R n
    _ = Waldhausen.KMap (positive_exact R) n :=
      Waldhausen.KMap_eq_of_iso (Euler.E0_exact R) (positive_exact R) (EulerE0PositiveIso R) n
    _ = _ := positive_KMap_eq_strictTotal R n

end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
