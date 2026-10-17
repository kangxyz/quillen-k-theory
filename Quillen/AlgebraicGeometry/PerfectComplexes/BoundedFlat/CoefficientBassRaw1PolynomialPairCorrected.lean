/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairInitial
public import Quillen.Aglib.Topology.Path.CarrierHalfPaths
public import Quillen.Topology.Path.CarrierSquareDescent

/-! The original cone reassociation and boundary descent on genuine polynomial inputs. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The initial corner of the polynomial-pair chart square. -/
def startPoint := chartSquare P β p q (0, 0)
/-- The top edge of the polynomial-pair chart square, parametrized by its second coordinate. -/
def chartTop : C(I, carrier P β p q) :=
  ⟨fun s ↦ chartSquare P β p q (1, s), by fun_prop⟩

/-- The lower boundary path of the initial cap, from the initial corner to the cone tip. -/
def lowerPath : Path (startPoint P β p q) (tip P β p q) where
  toFun s := initial P β p q (0, s)
  continuous_toFun := by fun_prop
  source' := initial_left P β p q 0
  target' := initial_right P β p q 0

/-- The chart-square path from the initial corner to the start of the top edge. -/
def leftPath : Path (startPoint P β p q) (chartTop P β p q 0) where
  toFun r := chartSquare P β p q (r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The first half of the chart-square top edge with the standard half-interval clock. -/
def firstPath := Path.CarrierHalfPaths.first (chartTop P β p q)
/-- The second half of the chart-square top edge with the standard half-interval clock. -/
def secondPath := Path.CarrierHalfPaths.last (chartTop P β p q)

/-- The final cylinder path from the end of the chart-square top edge to the cone tip. -/
def thirdPath : Path (chartTop P β p q 1) (tip P β p q) where
  toFun s := last P β p q (1, s)
  continuous_toFun := by fun_prop
  source' := (seam P β p q 1).symm
  target' := last_one P β p q 1

/-- The left-associated concatenation of the two chart-top halves and the final cylinder path. -/
def upperWord := ((firstPath P β p q).trans (secondPath P β p q)).trans (thirdPath P β p q)

theorem upperWord_apply (s : I) : upperWord P β p q s = initial P β p q (1, s) := by
  unfold upperWord
  rw [Path.trans_apply]
  change _ = ((firstSwap P β p q).trans (lastSwap P β p q)) (s, 1)
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact Path.CarrierHalfPaths.trans_apply (chartTop P β p q) _
  · rfl

/-- The initial carrier square with lower and upper boundary paths and constant right edge. -/
def initialSquare : CarrierPathSquare.Square (lowerPath P β p q) (upperWord P β p q)
    (leftPath P β p q) (Path.refl (tip P β p q)) where
  parameter := initial P β p q
  at_zero _ := rfl
  at_one s := (upperWord_apply P β p q s).symm
  left r := initial_left P β p q r
  right r := initial_right P β p q r

/-- Exactly the prescribed three-piece reassociation, with all old half clocks. -/
def correction := Path.Homotopy.transAssoc
  (firstPath P β p q) (secondPath P β p q) (thirdPath P β p q)
/-- The right-associated concatenation of the two chart-top halves and the final cylinder path. -/
def correctedUpper := (firstPath P β p q).trans ((secondPath P β p q).trans (thirdPath P β p q))

/-- The original boundary/correction word retains the constant-right reversal. -/
def correctedBoundary : (lowerPath P β p q).Homotopy
    (((leftPath P β p q).trans (correctedUpper P β p q)).trans
      (Path.refl (tip P β p q)).symm) :=
  (initialSquare P β p q).toBoundary.trans
    (((Path.Homotopy.refl (leftPath P β p q)).hcomp (correction P β p q)).hcomp
      ((Path.Homotopy.refl (Path.refl (tip P β p q))).symm))

/-- The carrier square with the reassociated upper boundary and constant right edge. -/
def correctedSquare : CarrierPathSquare.Square (lowerPath P β p q) (correctedUpper P β p q)
    (leftPath P β p q) (Path.refl (tip P β p q)) :=
  CarrierPathSquare.boundarySquare (correctedBoundary P β p q)

/-- The actual two-variable scalar cap after the original quotient correction. -/
def corrected : C(I × I, carrier P β p q) := (correctedSquare P β p q).parameter

theorem corrected_collapse (z : I × I) :
    corrected P β p q (ThreeSideSquare.collapse z) = correctedBoundary P β p q z :=
  CarrierPathSquare.boundaryParameter_collapse (correctedBoundary P β p q) z

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
