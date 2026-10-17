/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenAugmentation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! The two original polynomial sheets evaluate in the same original native Bass cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P a)
local notation "Q" => BassH0Merge.normalizedMap (laurentPlus P a)
local notation "F" => reference P a E
variable (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
  (space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (τ : (reference P a E).functor ≅ G.functor)
local notation "B" => FourEdgeTree.cone E J F (beta P a E)
local notation "j" => nerveMap (Codiscrete.functorOfFun (CommonReferenceProduct.reanchor τ)) ≫
  FourEdgeTree.coneLaurent E J F (beta P a E)
variable (ε₀ ε₁ : G.functor ≅
  (D ≫ BassH0Merge.normalizedMap (laurentPlus P a)).functor)

/-- The realized whole-reference cone with both original polynomial sheets attached. -/
abbrev augmentedScalar := |CutOpenAugmentation.simplicial D Q G ε₀ ε₁ B j|

/-- Both sheets keep their own scalar cylinder but the original positive native inclusion. -/
def originalSheetValue (n : ℕ) (z : |parameterSSet D| × TopCat.I.{u + 1})
    (x : (prespectrum V).space n) : (nativeBassCone P a).space n :=
  ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
    (z.2.down, LoopPrespectrum.HomotopyPushout.left (prespectrumMap J) (prespectrumMap J) n
      (pointwisePrespectrumFamily D n z.1 x))

theorem originalSheetValue_zero (ε : G.functor ≅ (D ≫ Q).functor) (n : ℕ)
    (y : |parameterSSet D|) :
    originalSheetValue P a D n (y, ULift.up 0) =
      coneEval P a E n (SSet.toTop.map (attaching D Q G ε ≫ j) y) := by
  funext x
  rw [FourEdgeTree.realized_comp, FourEdgeTree.realized_comp]
  change originalSheetValue P a D n (y, ULift.up 0) x =
    coneEval P a E n (FourEdgeTree.laurentInclusion E J F (beta P a E)
      (mapParameter (CommonReferenceProduct.reanchor τ)
        (SSet.toTop.map (attaching D Q G ε) y))) x
  rw [coneEval_laurent]
  dsimp only [originalSheetValue, laurentValue]
  rw [ReducedMappingCone.cylinder_zero, pointwise_reanchor]
  have h := pointwisePrespectrumFamily_attachPostcomp D Q G ε n y x
  change pointwisePrespectrumFamily G n (SSet.toTop.map (attaching D Q G ε) y) x =
    (prespectrumMap Q).map n (pointwisePrespectrumFamily D n y x) at h
  rw [h]; rfl

theorem originalSheetValue_one (n : ℕ) (y : |parameterSSet D|) :
    originalSheetValue P a D n (y, ULift.up 1) =
      fun _ ↦ (nativeBassCone P a).point n := by
  funext x
  exact ReducedMappingCone.cylinder_one _ _ _ _

/-- The ordinary polynomial sheet is attached to the already evaluated whole carrier. -/
def augmentedFirstEval (n : ℕ) :
    |CutOpenAugmentation.first D Q G ε₀ B j| →
      (prespectrum V).space n → (nativeBassCone P a).space n :=
  FourEdgeTree.SetDescent.value (attaching D Q G ε₀ ≫ j) (erase D)
    (coneEval P a E n) (fun _ _ ↦ (nativeBassCone P a).point n)
    (originalSheetValue P a D n) (originalSheetValue_zero P a E D G τ ε₀ n)
    (originalSheetValue_one P a D n)

theorem augmentedFirstEval_base (n : ℕ) (z : scalarCone P a E) :
    augmentedFirstEval P a E D G τ ε₀ n
      (SSet.toTop.map (CutOpenAugmentation.baseFirst D Q G ε₀ B j) z) =
      coneEval P a E n z := FourEdgeTree.SetDescent.value_left _ _ _ _ _ _ _ z

theorem secondSheet_zero (n : ℕ) (y : |parameterSSet D|) :
    originalSheetValue P a D n (y, ULift.up 0) =
      augmentedFirstEval P a E D G τ ε₀ n
        (SSet.toTop.map (CutOpenAugmentation.secondAttaching D Q G ε₀ ε₁ B j) y) := by
  rw [CutOpenAugmentation.secondAttaching, FourEdgeTree.realized_comp,
    FourEdgeTree.realized_comp, augmentedFirstEval_base]
  simpa only [FourEdgeTree.realized_comp] using originalSheetValue_zero P a E D G τ ε₁ n y

/-- Both original anchors and both separate scalar tips are retained by the final descent. -/
def augmentedEval (n : ℕ) :
    augmentedScalar P a E D G τ ε₀ ε₁ →
      (prespectrum V).space n → (nativeBassCone P a).space n :=
  FourEdgeTree.SetDescent.value
    (CutOpenAugmentation.secondAttaching D Q G ε₀ ε₁ B j) (erase D)
    (augmentedFirstEval P a E D G τ ε₀ n) (fun _ _ ↦ (nativeBassCone P a).point n)
    (originalSheetValue P a D n) (secondSheet_zero P a E D G τ ε₀ ε₁ n)
    (originalSheetValue_one P a D n)

theorem augmentedEval_first (n : ℕ) (z : |CutOpenAugmentation.first D Q G ε₀ B j|) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (SSet.toTop.map (CutOpenAugmentation.firstIn D Q G ε₀ ε₁ B j) z) =
      augmentedFirstEval P a E D G τ ε₀ n z :=
  FourEdgeTree.SetDescent.value_left _ _ _ _ _ _ _ z

theorem augmentedEval_base (n : ℕ) (z : scalarCone P a E) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (SSet.toTop.map (CutOpenAugmentation.baseIn D Q G ε₀ ε₁ B j) z) =
      coneEval P a E n z := by
  rw [CutOpenAugmentation.baseIn, FourEdgeTree.realized_comp, augmentedEval_first,
    augmentedFirstEval_base]

theorem augmentedEval_firstCylinder (n : ℕ) (y : |parameterSSet D|) (t : I)
    (x : (prespectrum V).space n) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (SSet.toTop.map (CutOpenAugmentation.firstIn D Q G ε₀ ε₁ B j)
        (DoubleCylinder.realizedCylinder (attaching D Q G ε₀ ≫ j) (erase D)
          (y, ULift.up t))) x = originalSheetValue P a D n (y, ULift.up t) x := by
  rw [augmentedEval_first]
  exact congrFun (FourEdgeTree.SetDescent.value_cylinder _ _ _ _ _ _ _ (y, ULift.up t)) x

theorem augmentedEval_secondCylinder (n : ℕ) (y : |parameterSSet D|) (t : I)
    (x : (prespectrum V).space n) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (DoubleCylinder.realizedCylinder
        (CutOpenAugmentation.secondAttaching D Q G ε₀ ε₁ B j) (erase D)
        (y, ULift.up t)) x = originalSheetValue P a D n (y, ULift.up t) x :=
  congrFun (FourEdgeTree.SetDescent.value_cylinder _ _ _ _ _ _ _ (y, ULift.up t)) x

theorem augmentedEval_firstTip (n : ℕ) (w : |tipSSet.{u + 1}|)
    (x : (prespectrum V).space n) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (SSet.toTop.map (CutOpenAugmentation.firstTip D Q G ε₀ B j ≫
        CutOpenAugmentation.firstIn D Q G ε₀ ε₁ B j) w) x = (nativeBassCone P a).point n := by
  rw [FourEdgeTree.realized_comp, augmentedEval_first]
  exact congrFun (FourEdgeTree.SetDescent.value_right _ _ _ _ _ _ _ w) x

theorem augmentedEval_secondTip (n : ℕ) (w : |tipSSet.{u + 1}|)
    (x : (prespectrum V).space n) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (SSet.toTop.map (CutOpenAugmentation.secondTip D Q G ε₀ ε₁ B j) w) x =
      (nativeBassCone P a).point n :=
  congrFun (FourEdgeTree.SetDescent.value_right _ _ _ _ _ _ _ w) x

theorem augmentedEval_laurent (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum V).space n) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (SSet.toTop.map (j ≫ CutOpenAugmentation.baseIn D Q G ε₀ ε₁ B j) y) x =
      (LoopPrespectrum.mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n
        (pointwisePrespectrumFamily G n y x) := by
  rw [FourEdgeTree.realized_comp, augmentedEval_base]
  rw [FourEdgeTree.realized_comp]
  change coneEval P a E n (FourEdgeTree.laurentInclusion E J F (beta P a E)
    (mapParameter (CommonReferenceProduct.reanchor τ) y)) x = _
  rw [coneEval_laurent]
  dsimp only [laurentValue]
  rw [pointwise_reanchor]

theorem originalSheetValue_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet D| × TopCat.I.{u + 1})) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      originalSheetValue P a D n (p z.1) z.2) := by
  let p' : C(S, |parameterSSet D|) := ⟨fun s ↦ (p s).1, by fun_prop⟩
  exact (ReducedMappingCone.cylinder _ _
    ((boundedFlatCoefficientBassSquareComparison P a).map n)).continuous.comp
      ((show Continuous (fun z : S × (prespectrum V).space n ↦ (p z.1).2.down) by
        fun_prop).prodMk
        ((LoopPrespectrum.HomotopyPushout.left
          (prespectrumMap J) (prespectrumMap J) n).continuous.comp
          (pointwisePrespectrumFamily_compact_continuous D p' n)))

theorem augmentedFirstEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |CutOpenAugmentation.first D Q G ε₀ B j|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      augmentedFirstEval P a E D G τ ε₀ n (p z.1) z.2) := by
  apply FourEdgeTree.SetDescent.value_compact_continuous
  · intro S _ _ q
    exact coneEval_compact_continuous P a E q n
  · intro S _ _ q
    exact continuous_const
  · intro S _ _ q
    exact originalSheetValue_compact_continuous P a D q n

theorem augmentedEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, augmentedScalar P a E D G τ ε₀ ε₁)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      augmentedEval P a E D G τ ε₀ ε₁ n (p z.1) z.2) := by
  apply FourEdgeTree.SetDescent.value_compact_continuous
  · intro S _ _ q
    exact augmentedFirstEval_compact_continuous P a E D G τ ε₀ q n
  · intro S _ _ q
    exact continuous_const
  · intro S _ _ q
    exact originalSheetValue_compact_continuous P a D q n

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
