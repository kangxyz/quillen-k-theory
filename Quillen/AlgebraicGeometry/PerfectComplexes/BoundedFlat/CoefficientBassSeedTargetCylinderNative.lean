/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetCylinderMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation
public import Quillen.Aglib.Topology.Path.HomotopyEvaluationTrans

/-! The exact original coefficient cone map on both whole carrier sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetCylinderNative
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassSeedTargetChartAttachment CoefficientBassSeedTargetCylinderMap

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

/-- Evaluate the target cut-open carrier using the positive chart and both target anchors. -/
abbrev evaluate := CutOpenCarrier.nativeEval (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
/-- The positive-chart square homotopy followed by inclusion into the target mapping cone. -/
abbrev chartHomotopy := (boundedFlatCoefficientPlusSquareHomotopy P f).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))
/-- The target positive-chart cone contraction precomposed with the polynomial coefficient map. -/
abbrev contractionHomotopy := Homotopy.precomp
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map f)))
  (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

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
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).map n)
    (CoefficientBassSeedTargetChartNative.moving_native P f D G
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

/-- Both original half clocks recover the prescribed positive cone-map null word. -/
theorem nullTrack_native (n : ℕ) (e : Bool) (t : I) (y : |parameterSSet D|)
    (x : (prespectrum V).space n) :
    evaluate P f D G ε₀ ε₁ n (nullTrack P f D G ε₀ ε₁ e (t, y)) x =
      (boundedFlatCoefficientBassPositiveConeMapNull P f).level n
        (t, pointwisePrespectrumFamily D n y x) :=
  ContinuousMap.Homotopy.Evaluation.trans_compare
    (chartTrack P f D G ε₀ ε₁ e) (contraction P f D G ε₀ ε₁ e)
    ((chartHomotopy P f).levelHomotopy n).toHomotopy
    ((contractionHomotopy P f).levelHomotopy n).toHomotopy
    (fun z ↦ evaluate P f D G ε₀ ε₁ n z x) id y
    (pointwisePrespectrumFamily D n y x)
    (fun s ↦ chartTrack_native P f D G ε₀ ε₁ n e s y x)
    (fun s ↦ contraction_native P f D G ε₀ ε₁ n e s y x) t

/-- The entire carrier map recovers the actual original positive coefficient cone map. -/
theorem map_native (n : ℕ) (z : sourceSpace P D G ε₀ ε₁)
    (x : (prespectrum V).space n) :
    evaluate P f D G ε₀ ε₁ n (CoefficientBassSeedTargetCylinderMap.map P f D G ε₀ ε₁ z) x =
      (boundedFlatCoefficientBassPositiveConeMap P f).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n z x) := by
  rcases exists_native_cell D (Ja P (a := a)) G ε₀ ε₁ z with
    ⟨y, rfl⟩ | ⟨y, t, rfl⟩ | ⟨y, t, rfl⟩ | rfl | rfl
  · rw [map_laurent, nativeEval_laurentInclusion]
    refine (nativeEval_laurentInclusion (D ≫ M P f) (Jb P) (G ≫ L P f)
      (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁) n _ x).trans ?_
    refine (congrArg ((mappingConeInclusion (prespectrumMap (Jb P))).map n)
      (pointwise_postcomp G (L P f) n y x)).trans ?_
    exact (congrArg (fun h ↦ h.map n (pointwisePrespectrumFamily G n y x))
      (boundedFlatCoefficientBassPositiveConeMap_inclusion P f)).symm
  · rw [map_cylinderMinus, nativeEval_cylinderMinus]
    exact (nullTrack_native P f D G ε₀ ε₁ n false t y x).trans
      (boundedFlatCoefficientBassPositiveConeMap_cylinder P f n t _).symm
  · rw [map_cylinderPlus, nativeEval_cylinderPlus]
    exact (nullTrack_native P f D G ε₀ ε₁ n true t y x).trans
      (boundedFlatCoefficientBassPositiveConeMap_cylinder P f n t _).symm
  · rw [map_tipMinus, nativeEval_tipMinus]
    exact (nativeEval_tipMinus _ _ _ _ _ n x).trans
      ((boundedFlatCoefficientBassPositiveConeMap P f).map_point n).symm
  · rw [map_tipPlus, nativeEval_tipPlus]
    exact (nativeEval_tipPlus _ _ _ _ _ n x).trans
      ((boundedFlatCoefficientBassPositiveConeMap P f).map_point n).symm

/-- After the original support inclusions this is literally the actual full Bass coefficient map. -/
theorem map_full_native (n : ℕ) (z : sourceSpace P D G ε₀ ε₁)
    (x : (prespectrum V).space n) :
    (boundedFlatCoefficientBassConeMap P f).map n
      ((boundedFlatCoefficientBassPositiveConeInclusion P a).map n
        (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n z x)) =
      (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
        (evaluate P f D G ε₀ ε₁ n
          (CoefficientBassSeedTargetCylinderMap.map P f D G ε₀ ε₁ z) x) :=
  (congrArg (fun h ↦ h.map n
    (CutOpenCarrier.nativeEval D (Ja P (a := a)) G ε₀ ε₁ n z x))
    (boundedFlatCoefficientBassPositiveConeMap_factor P f)).trans
      (congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P b).map n)
        (map_native P f D G ε₀ ε₁ n z x).symm)

end Quillen.PerfectComplexes.CoefficientBassSeedTargetCylinderNative
