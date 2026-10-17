/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetFirstMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetChartNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSupportMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation
public import Quillen.Aglib.Topology.Path.HomotopyEvaluationTrans

/-! The exact original coefficient cone map on both whole carrier sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNegativeTargetFirstNative
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassNegativeTargetChartAttachment CoefficientBassNegativeTargetFirstMap

private theorem pointwise_postcomp {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T)
    (n : ℕ) (y : |parameterSSet F|) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (F ≫ J) n (mapParameter (postcompNode J) y) x =
      (prespectrumMap J).map n (pointwisePrespectrumFamily F n y x) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact prespectrumFamily_postcomp N J n z x

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (Scheme.BaseChange.Coefficients.space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (Scheme.BaseChange.Coefficients.space (op P, (laurentUnderFunctor R).obj a))))
  (ε₀ ε₁ : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- Evaluate the target cut-open carrier using the negative chart and the two target anchors. -/
abbrev evaluate := CutOpenCarrier.nativeEval (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
/-- The negative-chart square homotopy followed by inclusion into the target mapping cone. -/
abbrev chartHomotopy := (boundedFlatCoefficientMinusSquareHomotopy P f).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentMinus P b)))
/-- The target negative-chart cone contraction precomposed with the polynomial coefficient map. -/
abbrev contractionHomotopy := Homotopy.precomp
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map f)))
  (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentMinus P b)))

/-- The chart part retains the entire original five-node square at every input. -/
theorem chartTrack_native (n : ℕ) (e : Bool) (t : I) (y : |parameterSSet D|)
    (x : (prespectrum V).space n) :
    evaluate P f D G ε₀ ε₁ n (chartTrack P f D G ε₀ ε₁ e (t, y)) x =
      (chartHomotopy P f).level n (t, pointwisePrespectrumFamily D n y x) := by
  change evaluate P f D G ε₀ ε₁ n
    (targetLaurent P f D G ε₀ ε₁
      (moving P f D G (sheetAnchor P D G ε₀ ε₁ e) (y, t))) x = _
  refine (nativeEval_laurentInclusion (D ≫ M P f) (Jb P) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁) n _ x).trans ?_
  exact congrArg ((mappingConeInclusion
    (boundedFlatPerfectPrespectrumMap (laurentMinus P b))).map n)
    (CoefficientBassNegativeTargetChartNative.moving_native P f D G
      (sheetAnchor P D G ε₀ ε₁ e) n y t x)

/-- The target contraction uses the actual polynomial coefficient action. -/
theorem contraction_native (n : ℕ) (e : Bool) (t : I) (y : |parameterSSet D|)
    (x : (prespectrum V).space n) :
    evaluate P f D G ε₀ ε₁ n (contraction P f D G ε₀ ε₁ e (t, y)) x =
      (contractionHomotopy P f).level n (t, pointwisePrespectrumFamily D n y x) := by
  cases e with
  | false =>
    change evaluate P f D G ε₀ ε₁ n
      (cylinderMinus _ _ _ _ _ (polynomialMap P f D y, t)) x = _
    refine (nativeEval_cylinderMinus (D ≫ M P f) (Jb P) (G ≫ L P f)
      (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁) n
      (polynomialMap P f D y) t x).trans ?_
    exact congrArg (fun z ↦ ReducedMappingCone.cylinder _ _ _ (t, z))
      (pointwise_postcomp D (M P f) n y x)
  | true =>
    change evaluate P f D G ε₀ ε₁ n
      (cylinderPlus _ _ _ _ _ (polynomialMap P f D y, t)) x = _
    refine (nativeEval_cylinderPlus (D ≫ M P f) (Jb P) (G ≫ L P f)
      (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁) n
      (polynomialMap P f D y) t x).trans ?_
    exact congrArg (fun z ↦ ReducedMappingCone.cylinder _ _ _ (t, z))
      (pointwise_postcomp D (M P f) n y x)

/-- Both original half clocks recover the prescribed negative cone-map null word. -/
theorem nullTrack_native (n : ℕ) (e : Bool) (t : I) (y : |parameterSSet D|)
    (x : (prespectrum V).space n) :
    evaluate P f D G ε₀ ε₁ n (nullTrack P f D G ε₀ ε₁ e (t, y)) x =
      (boundedFlatCoefficientBassNegativeConeMapNull P f).level n
        (t, pointwisePrespectrumFamily D n y x) :=
  ContinuousMap.Homotopy.Evaluation.trans_compare
    (chartTrack P f D G ε₀ ε₁ e) (contraction P f D G ε₀ ε₁ e)
    ((chartHomotopy P f).levelHomotopy n).toHomotopy
    ((contractionHomotopy P f).levelHomotopy n).toHomotopy
    (fun z ↦ evaluate P f D G ε₀ ε₁ n z x) id y
    (pointwisePrespectrumFamily D n y x)
    (fun s ↦ chartTrack_native P f D G ε₀ ε₁ n e s y x)
    (fun s ↦ contraction_native P f D G ε₀ ε₁ n e s y x) t

/-- Every point of the original first sheet recovers the actual negative coefficient map. -/
theorem firstMap_native (n : ℕ) (z : |firstSimplicial D (Ja P (a := a)) G ε₀|)
    (x : (prespectrum V).space n) :
    evaluate P f D G ε₀ ε₁ n (firstMap P f D G ε₀ ε₁ z) x =
      (boundedFlatCoefficientBassNegativeConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁) z) x) := by
  rcases Types.eq_or_eq_of_isPushout
    ((first_isPushout D (Ja P (a := a)) G ε₀).map (forget TopCat)) z with
    ⟨⟨y, t⟩, rfl⟩ | ⟨y | y, rfl⟩
  · change evaluate P f D G ε₀ ε₁ n (firstMap P f D G ε₀ ε₁
        (DoubleCylinder.realizedCylinder (attaching D (Ja P (a := a)) G ε₀)
        (erase D) (y, ULift.up t.down))) x =
      (boundedFlatCoefficientBassNegativeConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁)
            (DoubleCylinder.realizedCylinder (attaching D (Ja P (a := a)) G ε₀)
        (erase D) (y, ULift.up t.down))) x)
    rw [firstMap_cylinder]
    change _ = (boundedFlatCoefficientBassNegativeConeMap P f).map n
      (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
        (cylinderMinus D (Ja P (a := a)) G ε₀ ε₁ (y, t.down)) x)
    rw [nativeEval_cylinderMinus]
    exact (nullTrack_native P f D G ε₀ ε₁ n false t.down y x).trans
      (boundedFlatCoefficientBassNegativeConeMap_cylinder P f n t.down _).symm
  · change evaluate P f D G ε₀ ε₁ n (firstMap P f D G ε₀ ε₁
        (DoubleCylinder.realizedEnds (attaching D (Ja P (a := a)) G ε₀)
        (erase D) (Sum.inl y))) x =
      (boundedFlatCoefficientBassNegativeConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁)
            (DoubleCylinder.realizedEnds (attaching D (Ja P (a := a)) G ε₀)
        (erase D) (Sum.inl y))) x)
    rw [← FourEdgeTree.SetDescent.eval_realized_left]
    change evaluate P f D G ε₀ ε₁ n (firstMap P f D G ε₀ ε₁
      (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε₀) y)) x =
      (boundedFlatCoefficientBassNegativeConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (laurentInclusion D (Ja P (a := a)) G ε₀ ε₁ y) x)
    rw [firstMap_laurent]
    change _ = (boundedFlatCoefficientBassNegativeConeMap P f).map n
      (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
        (laurentInclusion D (Ja P (a := a)) G ε₀ ε₁ y) x)
    rw [nativeEval_laurentInclusion]
    refine (nativeEval_laurentInclusion (D ≫ M P f) (Jb P) (G ≫ L P f)
      (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁) n _ x).trans ?_
    refine (congrArg ((mappingConeInclusion (prespectrumMap (Jb P))).map n)
      (pointwise_postcomp G (L P f) n y x)).trans ?_
    exact (congrArg (fun h ↦ h.map n (pointwisePrespectrumFamily G n y x))
      (boundedFlatCoefficientBassNegativeConeMap_inclusion P f)).symm
  · have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
    subst y
    change evaluate P f D G ε₀ ε₁ n (firstMap P f D G ε₀ ε₁
        (DoubleCylinder.realizedEnds (attaching D (Ja P (a := a)) G ε₀)
        (erase D) (Sum.inr (default : |tipSSet.{u+1}|)))) x =
      (boundedFlatCoefficientBassNegativeConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁)
            (DoubleCylinder.realizedEnds (attaching D (Ja P (a := a)) G ε₀)
        (erase D) (Sum.inr (default : |tipSSet.{u+1}|)))) x)
    rw [← FourEdgeTree.SetDescent.eval_realized_right]
    have ht := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_right
      (SSet.toTop.map (attaching D (Ja P (a := a)) G ε₀))
      (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε₀)
      (laurentMap P f D G ε₀ ε₁)
      (ContinuousMap.const _ (tip P f D G ε₀ ε₁ false))
      (nullTrack P f D G ε₀ ε₁ false)) (default : |tipSSet.{u+1}|)
    have hr := (congrArg (firstMap P f D G ε₀ ε₁)
      (FourEdgeTree.SetDescent.eval_realized_right
        (attaching D (Ja P (a := a)) G ε₀) (erase D) _)).trans ht
    rw [hr]
    change evaluate P f D G ε₀ ε₁ n (tipMinus _ _ _ _ _) x =
      (boundedFlatCoefficientBassNegativeConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (tipMinus D (Ja P (a := a)) G ε₀ ε₁) x)
    rw [nativeEval_tipMinus]
    exact (nativeEval_tipMinus _ _ _ _ _ n x).trans
      ((boundedFlatCoefficientBassNegativeConeMap P f).map_point n).symm

/-- The supported first-sheet action is the literal original full Bass coefficient map. -/
theorem firstMap_full_native (n : ℕ) (z : |firstSimplicial D (Ja P (a := a)) G ε₀|)
    (x : (prespectrum V).space n) :
    (boundedFlatCoefficientBassConeMap P f).map n
      ((boundedFlatCoefficientBassNegativeConeInclusion P a).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
          (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁) z) x)) =
      (boundedFlatCoefficientBassNegativeConeInclusion P b).map n
        (evaluate P f D G ε₀ ε₁ n (firstMap P f D G ε₀ ε₁ z) x) :=
  (congrArg (fun h ↦ h.map n
    (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n
      (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁) z) x))
    (boundedFlatCoefficientBassNegativeConeMap_factor P f)).trans
      (congrArg ((boundedFlatCoefficientBassNegativeConeInclusion P b).map n)
        (firstMap_native P f D G ε₀ ε₁ n z x).symm)

end Quillen.PerfectComplexes.CoefficientBassNegativeTargetFirstNative
