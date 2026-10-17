/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputSourceMaps
public import Quillen.Topology.Path.ScalarRectangleConcatenation

/-! The second original height half retains its prescribed half-quarter-quarter overlap word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputSecond
open BassH0Merge BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "F" => TripleLaurent.input P p q w
local notation "Y" => FourEdge.scalarCone P d F

/-- The positive polynomial cap at the first original square endpoint. -/
def start : C(I × I, Y) :=
  ⟨fun z ↦ InputPolynomial.plusFamily P p q w (z, 0), by fun_prop⟩

/-- The negative polynomial cap at the same original square endpoint. -/
def finish : C(I × I, Y) :=
  ⟨fun z ↦ InputPolynomial.minusFamily P p q w (z, 0), by fun_prop⟩

/-- The entire zero-overlap face of the original central input family, retaining both other
clocks. -/
def middleLeft : C(I × I, Y) :=
  ⟨fun z ↦ InputCentral.family P p q w (z.1, (z.2, 0)), by fun_prop⟩

/-- The entire one-overlap face of the original central input family, retaining both other
clocks. -/
def middleRight : C(I × I, Y) :=
  ⟨fun z ↦ InputCentral.family P p q w (z.1, (z.2, 1)), by fun_prop⟩

/-- The positive source-square clock traverses its whole unchanged range. -/
def positive : (start P p q w).Homotopy (middleLeft P p q w) where
  toFun z := InputPolynomial.plusFamily P p q w (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left z := InputPolynomial.plusFamily_one P p q w z.1 z.2

/-- The central cap uses the original full overlap clock. -/
def central : (middleLeft P p q w).Homotopy (middleRight P p q w) where
  toFun z := InputCentral.family P p q w (z.2.1, (z.2.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The negative source-square clock is reversed only by the original outer word. -/
def negative : (finish P p q w).Homotopy (middleRight P p q w) where
  toFun z := InputPolynomial.minusFamily P p q w (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left z := InputPolynomial.minusFamily_one P p q w z.1 z.2

/-- The prescribed original span-map word, with its half-quarter-quarter cuts. -/
def word : (start P p q w).Homotopy (finish P p q w) :=
  (positive P p q w).trans ((central P p q w).trans (negative P p q w).symm)

/-- The second half is jointly continuous in comparison, outer height and overlap time. -/
def family : C(I × (I × I), Y) :=
  (word P p q w).toContinuousMap.comp
    ⟨fun z ↦ (z.2.2, (z.1, z.2.1)), by fun_prop⟩

theorem family_lower (r h t : I) : family P p q w (r, (h, lower t)) =
    InputPolynomial.plusFamily P p q w ((r, h), t) :=
  ScalarRectangle.homotopy_lower (positive P p q w)
    ((central P p q w).trans (negative P p q w).symm) t (r, h)

theorem family_middle (r h t : I) : family P p q w (r, (h, upper (lower t))) =
    InputCentral.family P p q w (r, (h, t)) := by
  change word P p q w (upper (lower t), (r, h)) = _
  unfold word
  rw [ScalarRectangle.homotopy_upper, ScalarRectangle.homotopy_lower]
  rfl

theorem family_upper (r h t : I) : family P p q w (r, (h, upper (upper t))) =
    InputPolynomial.minusFamily P p q w ((r, h), unitInterval.symm t) := by
  change word P p q w (upper (upper t), (r, h)) = _
  unfold word
  rw [ScalarRectangle.homotopy_upper, ScalarRectangle.homotopy_upper]
  rfl

theorem family_zero (r h : I) : family P p q w (r, (h, 0)) =
    InputPolynomial.plusFamily P p q w ((r, h), 0) :=
  (word P p q w).map_zero_left (r, h)

theorem family_one (r h : I) : family P p q w (r, (h, 1)) =
    InputPolynomial.minusFamily P p q w ((r, h), 0) :=
  (word P p q w).map_one_left (r, h)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputSecond
