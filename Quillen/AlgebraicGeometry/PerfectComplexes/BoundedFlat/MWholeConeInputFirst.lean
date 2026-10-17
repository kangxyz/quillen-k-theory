/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLaurentPlacement
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers

/-! The exact first height half of the ordinary input cap in its fixed triple cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputLaurentProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassH0Merge BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The first original height half uses the Laurent inclusion of the same ordinary cone. -/
def first : C(I × (FourEdgeTree.space E (normalizedMap (polynomialProjection P a)) × I),
    FourEdge.scalarCone P d (fixedInput P p q w E)) :=
  (FourEdgeTree.laurentInclusion (fixedInput P p q w E)
    (normalizedMap (polynomialProjection P d)) (reference P d (fixedInput P p q w E))
    (FourEdge.beta P d (fixedInput P p q w E))).comp (placedFamily P p q w E)

/-- The full midpoint target is the original Laurent binary family over beta of treeMap. -/
theorem first_target (r : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) :
    first P p q w E (r, (z, 1)) =
      FourEdgeTree.laurentInclusion (fixedInput P p q w E)
        (normalizedMap (polynomialProjection P d)) (reference P d (fixedInput P p q w E))
        (FourEdge.beta P d (fixedInput P p q w E))
        (place P p q w E (product P p q w E
          (SSet.toTop.map (FourEdge.beta P b (E ≫ normalizedMap (coefficientMap P p)))
            (FourEdge.TargetSpan.treeMap P p E z), r))) :=
  congrArg (FourEdgeTree.laurentInclusion (fixedInput P p q w E)
    (normalizedMap (polynomialProjection P d)) (reference P d (fixedInput P p q w E))
    (FourEdge.beta P d (fixedInput P p q w E))) (placedFamily_target P p q w E r z)

/-- The first half recovers the literal original cone K on its Laurent input at every level. -/
theorem first_native (n : ℕ) (r s : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a)))
    (x : (prespectrum V).space n) :
    FourEdge.coneEval P d (fixedInput P p q w E) n (first P p q w E (r, (z, s))) x =
      (BassMWhole.coneComposition P q w).level n
        (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
          ((boundedFlatCoefficientBassComparisonHomotopy P p).level n
            (s, FourEdgeTree.nativeEval E (normalizedMap (polynomialProjection P a)) n z x))) := by
  change FourEdge.coneEval P d (fixedInput P p q w E) n
    (FourEdgeTree.laurentInclusion _ _ _ _ (placedFamily P p q w E (r, (z, s)))) x = _
  rw [FourEdge.coneEval_laurent]
  change (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).map n
    (pointwisePrespectrumFamily _ n (placedFamily P p q w E (r, (z, s))) x) = _
  rw [placedFamily_native, BassMWhole.cone_inclusion]
  rfl

/-- The source outer height is precisely the original lower half, with no changed clock. -/
theorem first_native_lower (n : ℕ) (r s : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a)))
    (x : (prespectrum V).space n) :
    FourEdge.coneEval P d (fixedInput P p q w E) n (first P p q w E (r, (z, s))) x =
      (BassMWhole.coneComposition P q w).level n
        (r, (boundedFlatCoefficientBassConeMap P p).map n
          (ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
            (Quillen.NativePathCells.lower s,
              FourEdgeTree.nativeEval E (normalizedMap (polynomialProjection P a)) n z x))) := by
  rw [boundedFlatCoefficientBassConeMap_cylinder, Homotopy.trans_lower_cell]
  exact first_native P p q w E n r s z x

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputLaurentProduct
