/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeMovingPieces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionBeta

/-! The original M moving-null square pasted at its proved whole-reference seam. -/
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

/-- This is a whole carrier attachment, using the actual M reference and frozen top face. -/
theorem seam (r t : I) : cube P p q (r, (1, t)) = last P p q (r, (0, t)) := by
  dsimp only [cube, last, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [FourEdgeTree.cone_cylinder_zero, laurentCube_top,
    CoefficientBassSpanCompositionReference.treeComposition_beta]

/-- The initial face of the cone cube, retaining the outer and overlap parameters. -/
def leftEdge : C(I × I, FourEdge.scalarCone P c E) :=
  ⟨fun z ↦ cube P p q (z.1, (0, z.2)), by fun_prop⟩
/-- The terminal face of the cone cube, shared with the initial cylinder face. -/
def middleEdge : C(I × I, FourEdge.scalarCone P c E) :=
  ⟨fun z ↦ cube P p q (z.1, (1, z.2)), by fun_prop⟩
/-- The constant face at the unreduced four-edge cone tip. -/
def rightEdge : C(I × I, FourEdge.scalarCone P c E) :=
  ContinuousMap.const _ (FourEdgeTree.tip E J F β)

/-- The cone-cube homotopy from the initial face to the shared middle face. -/
def firstSwap : (leftEdge P p q).Homotopy (middleEdge P p q) where
  toFun z := cube P p q (z.2.1, (z.1, z.2.2))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The cylinder homotopy from the shared middle face to the constant tip face. -/
def lastSwap : (middleEdge P p q).Homotopy (rightEdge P p q) where
  toFun z := last P p q (z.2.1, (z.1, z.2.2))
  continuous_toFun := by fun_prop
  map_zero_left z := (seam P p q z.1 z.2).symm
  map_one_left z := last_one P p q z.1 z.2

/-- The original two halves are pasted jointly in all three scalar coordinates. -/
def initial : C(I × (I × I), FourEdge.scalarCone P c E) :=
  ⟨fun z ↦ ((firstSwap P p q).trans (lastSwap P p q)) (z.2.1, (z.1, z.2.2)),
    by fun_prop⟩

theorem initial_left (r t : I) : initial P p q (r, (0, t)) = cube P p q (r, (0, t)) :=
  ((firstSwap P p q).trans (lastSwap P p q)).apply_zero (r, t)

theorem initial_right (r t : I) :
    initial P p q (r, (1, t)) = FourEdgeTree.tip E J F β :=
  ((firstSwap P p q).trans (lastSwap P p q)).apply_one (r, t)

/-- The exact original moving-null square is recovered on every overlap input and degree. -/
theorem initial_native (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P c E n (initial P p q (r, (s, t))) x =
      (initialNative P p q).level n (r, (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) := by
  change FourEdge.coneEval P c E n
    (((firstSwap P p q).trans (lastSwap P p q)) (s, (r, t))) x = _
  rw [ContinuousMap.Homotopy.trans_apply, initialNative, coneSquareNullMovingSquare_apply]
  split_ifs
  · rw [BassMWhole.comparison_cylinder]
    exact cube_native P p q n r _ t x
  · exact last_native P p q n r _ t x

end Quillen.PerfectComplexes.BassMWholeConeCarrier
