/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePostcompCap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetConeNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeLaws

/-! The fixed-reference ordinary cap recovers the unchanged postcomposed M cone homotopy. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
open BassH0Merge CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => inputReference P p q
local notation "V" => modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))

/-- Native values retain the actual coefficient map through the complete input reanchor. -/
theorem carrierMap_native (n : ℕ) (z : FourEdge.scalarCone P c E)
    (x : (prespectrum V).space n) :
    FourEdge.coneEval P d (input P p q w) n (carrierMap P p q w z) x =
      (boundedFlatCoefficientBassConeMap P w).map n (FourEdge.coneEval P c E n z x) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  exact (FourEdge.Reanchor.cone_native P d (mappedInput P p q w) (input P p q w)
    (inputIso P p q w) n (FourEdge.TargetCone.coneMap P w E z) x).trans
      (FourEdge.TargetCone.coneMap_native P w E n z x)

/-- The actual postcomposed original cone-composition cylinder, at all independent clocks. -/
theorem cap_native (n : ℕ) (r s t : I) (x : (prespectrum V).space n) :
    FourEdge.coneEval P d (input P p q w) n (cap P p q w (r, (s, t))) x =
      (boundedFlatCoefficientBassConeMap P w).map n
        ((BassMWhole.coneComposition P p q).level n
          (r, ReducedMappingCone.cylinder _ _
            ((boundedFlatCoefficientBassSquareComparison P a).map n)
            (s, BassMWholeConeCarrier.input P (a := a) n t x))) := by
  change FourEdge.coneEval P d (input P p q w) n
    (carrierMap P p q w (corrected P p q (r, (s, t)))) x = _
  rw [carrierMap_native, coneComposition_cylinder]

/-- Compactness is only required of the scalar parameter family. -/
theorem cap_native_continuous (n : ℕ) :
    Continuous (fun z : (I × (I × I)) × (prespectrum V).space n ↦
      FourEdge.coneEval P d (input P p q w) n (cap P p q w z.1) z.2) :=
  FourEdge.coneEval_compact_continuous P d (input P p q w) (cap P p q w) n

/-- The genuine native base point is retained for every scalar cap coordinate. -/
theorem cap_native_point (n : ℕ) (z : I × (I × I)) :
    FourEdge.coneEval P d (input P p q w) n (cap P p q w z) ((prespectrum V).point n) =
      (FourEdge.nativeBassCone P d).point n :=
  FourEdge.coneEval_point P d (input P p q w) n (cap P p q w z)

/-- The structure-loop time is independent of all three cap coordinates. -/
theorem cap_native_structure (n : ℕ) (z : I × (I × I))
    (x : (prespectrum V).space n) (v : I) :
    FourEdge.coneEval P d (input P p q w) (n + 1) (cap P p q w z)
      ((prespectrum V).structureMap n x v) =
    (FourEdge.nativeBassCone P d).structureMap n
      (FourEdge.coneEval P d (input P p q w) n (cap P p q w z) x) v :=
  FourEdge.coneEval_structure P d (input P p q w) n (cap P p q w z) x v

end Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
