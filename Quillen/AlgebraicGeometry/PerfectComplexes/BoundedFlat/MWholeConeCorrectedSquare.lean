/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInitialSquare
public import Quillen.Aglib.Topology.Path.CarrierHalfPaths
public import Quillen.Topology.Path.CarrierSquareDescent

/-! The original cone correction in the compact overlap mapping space. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier
open CommonReferenceNerve BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => inputReference P p q
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P c)
local notation "F" => reference P c E
local notation "β" => FourEdge.beta P c E
local notation "X" => FourEdge.scalarCone P c E

/-- The extra compact coordinate remains the original overlap time throughout the correction. -/
def initialCurried : C(I × I, C(I, X)) := ContinuousMap.curry
  ⟨fun z : (I × I) × I ↦ initial P p q (z.1.1, (z.1.2, z.2)), by fun_prop⟩

/-- The initial corner of the cone cube, retained as a family in the overlap time. -/
def startPoint : C(I, X) := ⟨fun t ↦ cube P p q (0, (0, t)), by fun_prop⟩
/-- The constant family at the unreduced cone tip. -/
def endTip : C(I, X) := ContinuousMap.const _ (FourEdgeTree.tip E J F β)
/-- The top face of the cone cube, curried as a path of overlap-time families. -/
def chartTop : C(I, C(I, X)) := ContinuousMap.curry
  ⟨fun z : I × I ↦ cube P p q (1, (z.1, z.2)), by fun_prop⟩

/-- The lower boundary path from the initial overlap-time family to the constant tip family. -/
def lowerPath : Path (startPoint P p q) (endTip P p q) where
  toFun s := initialCurried P p q (0, s)
  continuous_toFun := by fun_prop
  source' := by
    ext t
    exact initial_left P p q 0 t
  target' := by
    ext t
    exact initial_right P p q 0 t

/-- The left boundary path from the initial family to the start of the chart-top path. -/
def leftPath : Path (startPoint P p q) (chartTop P p q 0) where
  toFun r := ⟨fun t ↦ cube P p q (r, (0, t)), by fun_prop⟩
  continuous_toFun := by
    exact (ContinuousMap.curry
      ⟨fun z : I × I ↦ cube P p q (z.1, (0, z.2)), by fun_prop⟩).continuous
  source' := rfl
  target' := rfl

/-- The first half of the chart-top path in the space of overlap-time families. -/
def firstPath := Path.CarrierHalfPaths.first (chartTop P p q)
/-- The second half of the chart-top path in the space of overlap-time families. -/
def secondPath := Path.CarrierHalfPaths.last (chartTop P p q)

/-- The final cylinder path from the chart-top endpoint to the constant tip family. -/
def thirdPath : Path (chartTop P p q 1) (endTip P p q) where
  toFun s := ⟨fun t ↦ last P p q (1, (s, t)), by fun_prop⟩
  continuous_toFun := by
    exact (ContinuousMap.curry
      ⟨fun z : I × I ↦ last P p q (1, (z.1, z.2)), by fun_prop⟩).continuous
  source' := by
    ext t
    exact (seam P p q 1 t).symm
  target' := by
    ext t
    exact last_one P p q 1 t

/-- The left-associated concatenation of the chart-top halves and final cylinder path. -/
def upperWord := ((firstPath P p q).trans (secondPath P p q)).trans (thirdPath P p q)

theorem upperWord_apply (s : I) : upperWord P p q s = initialCurried P p q (1, s) := by
  ext t
  unfold upperWord
  rw [Path.trans_apply]
  change _ = ((firstSwap P p q).trans (lastSwap P p q)) (s, (1, t))
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact congrArg (fun f : C(I, X) ↦ f t) (Path.CarrierHalfPaths.trans_apply (chartTop P p q) _)
  · rfl

/-- The initial square of overlap-time families with the original upper-boundary association. -/
def initialSquare : CarrierPathSquare.Square (lowerPath P p q) (upperWord P p q)
    (leftPath P p q) (Path.refl (endTip P p q)) where
  parameter := initialCurried P p q
  at_zero _ := rfl
  at_one s := (upperWord_apply P p q s).symm
  left r := by
    ext t
    exact initial_left P p q r t
  right r := by
    ext t
    exact initial_right P p q r t

/-- Only the original three path parentheses change. -/
def correction := Path.Homotopy.transAssoc
  (firstPath P p q) (secondPath P p q) (thirdPath P p q)
/-- The right-associated concatenation of the chart-top halves and final cylinder path. -/
def correctedUpper := (firstPath P p q).trans ((secondPath P p q).trans (thirdPath P p q))

/-- The original boundary/correction/descent word includes the constant-right reversal. -/
def correctedBoundary : (lowerPath P p q).Homotopy
    (((leftPath P p q).trans (correctedUpper P p q)).trans
      (Path.refl (endTip P p q)).symm) :=
  (initialSquare P p q).toBoundary.trans
    (((Path.Homotopy.refl (leftPath P p q)).hcomp (correction P p q)).hcomp
      ((Path.Homotopy.refl (Path.refl (endTip P p q))).symm))

/-- The corrected square of overlap-time families with the reassociated upper boundary. -/
def correctedSquare : CarrierPathSquare.Square (lowerPath P p q) (correctedUpper P p q)
    (leftPath P p q) (Path.refl (endTip P p q)) :=
  CarrierPathSquare.boundarySquare (correctedBoundary P p q)

/-- Joint scalar continuity follows by evaluation of the compact mapping-space square. -/
def corrected : C(I × (I × I), X) :=
  ⟨fun z ↦ (correctedSquare P p q).parameter (z.1, z.2.1) z.2.2, by fun_prop⟩

theorem corrected_collapse (z : I × I) (t : I) :
    corrected P p q ((ThreeSideSquare.collapse z).1, ((ThreeSideSquare.collapse z).2, t)) =
      correctedBoundary P p q z t :=
  congrArg (fun f : C(I, X) ↦ f t)
    (CarrierPathSquare.boundaryParameter_collapse (correctedBoundary P p q) z)

end Quillen.PerfectComplexes.BassMWholeConeCarrier
