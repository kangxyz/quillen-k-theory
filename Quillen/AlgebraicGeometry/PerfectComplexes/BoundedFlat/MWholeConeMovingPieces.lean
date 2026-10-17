/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionLift
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers
public import Quillen.Topology.Prespectrum.ConeSquareMovingNullEvaluation

/-! The two exact pieces of the original M moving-null square. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
open CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => inputReference P p q
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P c)
local notation "F" => reference P c E
local notation "β" => FourEdge.beta P c E

/-- The original target cone homotopy is evaluated at the actual moving span A. -/
def last : C(I × (I × I), FourEdge.scalarCone P c E) :=
  (FourEdgeTree.cylinder E J F β).comp
    ⟨fun z ↦ (CoefficientBassSpanCompositionReference.treeComposition P p q (z.1, z.2.2),
      z.2.1), by fun_prop⟩

theorem last_native (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P c E n (last P p q (r, (s, t))) x =
      ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P c).map n)
        (s, (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
          (r, HomotopyPushout.cylinder
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) := by
  dsimp only [last, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [FourEdge.coneEval_cylinder,
    CoefficientBassSpanCompositionReference.treeComposition_native]

/-- The exact existing initial square, before its prescribed reassociation correction. -/
abbrev initialNative := coneSquareNullMovingSquare
  (boundedFlatCoefficientBassSquareComparison P a)
  (boundedFlatCoefficientBassSquareComparison P c)
  (boundedFlatCoefficientBassComparisonHomotopy P (p ≫ q))
  (boundedFlatCoefficientBassCompositeComparison P p q)
  (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q)
  (boundedFlatCoefficientLaurentCompositionHomotopy P p q)
  (BassMWhole.comparisonSquare P p q)

/-- The scalar last piece ends at the actual unreduced tip for every r and t. -/
theorem last_one (r t : I) : last P p q (r, (1, t)) = FourEdgeTree.tip E J F β := by
  dsimp only [last, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  exact FourEdgeTree.cone_cylinder_one E J F β _

end Quillen.PerfectComplexes.BassMWholeConeCarrier
