/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassCutOpenAugmentationEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenAugmentationTopology
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupport
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

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

/-- The whole original two-sheet carrier retains its exact native positive-cone image. -/
theorem augmentedEval_originalMap (n : ℕ)
    (y : CutOpenCarrier.space D Q G ε₀ ε₁) (x : (prespectrum V).space n) :
    augmentedEval P a E D G τ ε₀ ε₁ n
      (CutOpenAugmentation.continuousMap D Q G ε₀ ε₁ B j y) x =
        (boundedFlatCoefficientBassPositiveConeInclusion P a).map n
          (CutOpenCarrier.nativeEval D Q G ε₀ ε₁ n y x) := by
  rcases CutOpenCarrier.exists_native_cell D Q G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, t, rfl⟩ | ⟨z, t, rfl⟩ | rfl | rfl
  · rw [CutOpenAugmentation.continuousMap_laurent,
      CutOpenCarrier.nativeEval_laurentInclusion]
    exact augmentedEval_laurent P a E D G τ ε₀ ε₁ n z x
  · rw [CutOpenAugmentation.continuousMap_cylinderMinus,
      CutOpenCarrier.nativeEval_cylinderMinus]
    exact augmentedEval_firstCylinder P a E D G τ ε₀ ε₁ n z t x
  · rw [CutOpenAugmentation.continuousMap_cylinderPlus,
      CutOpenCarrier.nativeEval_cylinderPlus]
    exact augmentedEval_secondCylinder P a E D G τ ε₀ ε₁ n z t x
  · rw [CutOpenAugmentation.continuousMap_tipMinus, CutOpenCarrier.nativeEval_tipMinus]
    dsimp only [CutOpenAugmentation.tipMinus]
    rw [augmentedEval_first]
    exact (congrFun (FourEdgeTree.SetDescent.value_right _ _ _ _ _ _ _ _) x).trans
      ((boundedFlatCoefficientBassPositiveConeInclusion P a).map_point n).symm
  · rw [CutOpenAugmentation.continuousMap_tipPlus, CutOpenCarrier.nativeEval_tipPlus]
    exact (augmentedEval_secondTip P a E D G τ ε₀ ε₁ n _ x).trans
      ((boundedFlatCoefficientBassPositiveConeInclusion P a).map_point n).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
