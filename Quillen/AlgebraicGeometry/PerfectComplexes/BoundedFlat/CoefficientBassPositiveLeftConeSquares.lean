/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftCellParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import Quillen.Topology.Path.CarrierSquareBoundary
public import Quillen.Topology.Path.ScalarPathCells

/-!
# Four finite left-route cone squares

The A squares paste the finite 25-node chart to the P cylinder, in the original cone-map
half clocks. The B squares are the Q cylinders. They are continuous in the actual common
carrier and end at its two separate tips. This constructs no map on an entire cone carrier.
-/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftConeSquares
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftPolynomialParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Each sheet has its own continuous polynomial cylinder and its own tip. -/
def cylinder (e : Bool) : C(|nerve (Codiscrete (Node (polynomialReference P p q)))| × I,
    Carrier P p q) := if e then plusCylinder P p q else minusCylinder P p q
def tip (e : Bool) : Carrier P p q := if e then plusTip P p q else minusTip P p q

theorem cylinder_zero (e : Bool)
    (y : |nerve (Codiscrete (Node (polynomialReference P p q)))|) :
    cylinder P p q e (y, 0) =
      includeLaurent P p q (mapParameter (attach P p q e) y) := by
  cases e
  · exact CutOpenCarrier.cylinderMinus_zero _ _ _ _ _ _
  · exact CutOpenCarrier.cylinderPlus_zero _ _ _ _ _ _

theorem cylinder_one (e : Bool)
    (y : |nerve (Codiscrete (Node (polynomialReference P p q)))|) :
    cylinder P p q e (y, 1) = tip P p q e := by
  cases e
  · exact CutOpenCarrier.cylinderMinus_one _ _ _ _ _ _
  · exact CutOpenCarrier.cylinderPlus_one _ _ _ _ _ _

theorem tips_distinct : tip P p q false ≠ tip P p q true :=
  CutOpenCarrier.tips_ne _ _ _ _ _

def chartStart (e : Bool) : C(I, Carrier P p q) :=
  ⟨fun t ↦ includeLaurent P p q (Z P p q e (t, 0)), by fun_prop⟩
def chartEnd (e : Bool) : C(I, Carrier P p q) :=
  ⟨fun t ↦ includeLaurent P p q (Z P p q e (t, 1)), by fun_prop⟩

def chartHomotopy (e : Bool) : (chartStart P p q e).Homotopy (chartEnd P p q e) where
  toFun z := includeLaurent P p q (Z P p q e (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- S2 in the actual quotient: the original full attachment licenses this continuous paste. -/
def firstContraction (e : Bool) : (chartEnd P p q e).Homotopy
    (ContinuousMap.const I (tip P p q e)) where
  toFun z := cylinder P p q e (firstParameter P p q z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left t := (cylinder_zero P p q e _).trans
    (congrArg (includeLaurent P p q) (Z_attach_first P p q e t).symm)
  map_one_left _ := cylinder_one P p q e _

/-- The first cone square uses the literal original half-time concatenation. -/
def A (e : Bool) : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ ((chartHomotopy P p q e).trans (firstContraction P p q e)) (z.2, z.1),
    by fun_prop⟩

/-- The second square is the actual Q family crossed with its sheet's cone interval. -/
def B (e : Bool) : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ cylinder P p q e (secondParameter P p q z.1, z.2), by fun_prop⟩

abbrev Aminus := A P p q false
abbrev Aplus := A P p q true
abbrev Bminus := B P p q false
abbrev Bplus := B P p q true

def chartPath (e : Bool) (t : I) :
    Path (chartStart P p q e t) (chartEnd P p q e t) where
  toFun s := includeLaurent P p q (Z P p q e (t, s))
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def firstCylinderPath (e : Bool) (t : I) :
    Path (chartEnd P p q e t) (tip P p q e) where
  toFun s := cylinder P p q e (firstParameter P p q t, s)
  continuous_toFun := by fun_prop
  source' := (firstContraction P p q e).apply_zero t
  target' := cylinder_one P p q e _

def APath (e : Bool) (t : I) : Path (chartStart P p q e t) (tip P p q e) :=
  (chartPath P p q e t).trans (firstCylinderPath P p q e t)

/-- The transposed continuous paste is precisely the ordinary path concatenation. -/
theorem A_path (e : Bool) (t s : I) : A P p q e (t, s) = APath P p q e t s := by
  change ((chartHomotopy P p q e).trans (firstContraction P p q e)) (s, t) =
    ((chartPath P p q e t).trans (firstCylinderPath P p q e t)) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]; rfl

/-- The original first half is exactly chart time s at cone time s/2. -/
theorem A_lower (e : Bool) (t s : I) :
    A P p q e (t, Quillen.NativePathCells.lower s) =
      includeLaurent P p q (Z P p q e (t, s)) := by
  rw [A_path]
  exact Quillen.NativePathCells.path_lower _ _ s

/-- The original second half is exactly cylinder time s at cone time (s+1)/2. -/
theorem A_upper (e : Bool) (t s : I) :
    A P p q e (t, Quillen.NativePathCells.upper s) =
      cylinder P p q e (firstParameter P p q t, s) := by
  rw [A_path]
  exact Quillen.NativePathCells.path_upper _ _ s

/-- S1 as a whole carrier lower edge, on each separate sheet. -/
theorem A_left (e : Bool) (t : I) : A P p q e (t, 0) =
    includeLaurent P p q (firstMovement P p q e t) := by
  rw [A_path, Path.source, first_movement_Z]; rfl

theorem A_right (e : Bool) (t : I) : A P p q e (t, 1) = tip P p q e := by
  rw [A_path, Path.target]

/-- S3 as a whole carrier lower edge, before any unit-edge or seed comparison. -/
theorem B_left (e : Bool) (t : I) : B P p q e (t, 0) =
    includeLaurent P p q (secondMovement P p q e t) := by
  change cylinder P p q e (_, 0) = _
  rw [cylinder_zero, second_movement_attach]

theorem B_right (e : Bool) (t : I) : B P p q e (t, 1) = tip P p q e :=
  cylinder_one P p q e _

def firstLowerPath (e : Bool) :
    Path (chartStart P p q e 0) (chartStart P p q e 1) where
  toFun t := chartStart P p q e t
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- A± as genuine squares with their entire boundary paths and constant respective tips. -/
def ASquare (e : Bool) : Quillen.CarrierPathSquare.Square
    (APath P p q e 0) (APath P p q e 1)
    (firstLowerPath P p q e) (Path.refl (tip P p q e)) where
  parameter := A P p q e
  at_zero := A_path P p q e 0
  at_one := A_path P p q e 1
  left t := (A_path P p q e t 0).trans (APath P p q e t).source
  right := A_right P p q e

def BPath (e : Bool) (t : I) :
    Path (includeLaurent P p q (secondMovement P p q e t)) (tip P p q e) where
  toFun s := B P p q e (t, s)
  continuous_toFun := by fun_prop
  source' := B_left P p q e t
  target' := B_right P p q e t

def secondLowerPath (e : Bool) :
    Path (includeLaurent P p q (secondMovement P p q e 0))
      (includeLaurent P p q (secondMovement P p q e 1)) where
  toFun t := includeLaurent P p q (secondMovement P p q e t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- B± as genuine squares, retaining the original unrescaled cylinder coordinate. -/
def BSquare (e : Bool) : Quillen.CarrierPathSquare.Square
    (BPath P p q e 0) (BPath P p q e 1)
    (secondLowerPath P p q e) (Path.refl (tip P p q e)) where
  parameter := B P p q e
  at_zero _ := rfl
  at_one _ := rfl
  left := B_left P p q e
  right := B_right P p q e

/-- The S4 chart/cylinder join uses the complete P(1)=Q(0) nerve equation. -/
theorem middle_attachment (e : Bool) :
    includeLaurent P p q (middleChart P p q e 1) = B P p q e (0, 0) := by
  rw [← Z_target_middle_chart, Z_attach_first, polynomial_time_seam]
  exact (cylinder_zero P p q e (secondParameter P p q 0)).symm

def middleChartPath (e : Bool) :
    Path (includeLaurent P p q (middleChart P p q e 0))
      (includeLaurent P p q (middleChart P p q e 1)) where
  toFun s := includeLaurent P p q (middleChart P p q e s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def middleCylinderPath (e : Bool) :
    Path (includeLaurent P p q (middleChart P p q e 1)) (tip P p q e) where
  toFun s := B P p q e (0, s)
  continuous_toFun := by fun_prop
  source' := (middle_attachment P p q e).symm
  target' := B_right P p q e 0

/-- The complete time-seam null tail has exactly L.trans cylinder(Q(0)). -/
def middleNull (e : Bool) := (middleChartPath P p q e).trans (middleCylinderPath P p q e)

/-- S4 whole null tail, with no reassociation, unit assumption, or seed identification. -/
theorem A_time_seam (e : Bool) (s : I) : A P p q e (1, s) = middleNull P p q e s := by
  rcases Quillen.NativePathCells.cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [A_lower, middleNull, Quillen.NativePathCells.path_lower]
    exact congrArg (includeLaurent P p q) (Z_target_middle_chart P p q e t)
  · rw [A_upper, polynomial_time_seam, middleNull, Quillen.NativePathCells.path_upper]; rfl

/-- The original first new-positive binary path ends at the actual A(1) source. -/
def firstNewPositive (e : Bool) :
    Path (includeLaurent P p q (parameter (laurentReference P p q)
      (firstRectangleNodes P p q e)
      (ProjectionRectangleParameters.K BassH0Diagram.plusFace 0)))
      (chartStart P p q e 1) where
  toFun s := includeLaurent P p q (parameter (laurentReference P p q)
    (firstRectangleNodes P p q e)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace s))
  continuous_toFun := by fun_prop
  source' := rfl
  target' := by
    change includeLaurent P p q (parameter _ _ _) =
      includeLaurent P p q (Z P p q e (1, 0))
    rw [← first_movement_Z]
    change includeLaurent P p q (parameter _ _
      (ProjectionRectangleParameters.K BassH0Diagram.plusFace 1)) =
        includeLaurent P p q (parameter _ _
          (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace 1))
    rw [Path.target, Path.target]

/-- The original middle old-positive binary path ends at the actual middle chart source. -/
def middleOldPositive (e : Bool) :
    Path (includeLaurent P p q (parameter (laurentReference P p q)
      (middleRectangleNodes P p q e)
      (ProjectionRectangleParameters.D BassH0Diagram.plusFace 0)))
      (includeLaurent P p q (middleChart P p q e 0)) where
  toFun s := includeLaurent P p q (parameter (laurentReference P p q)
    (middleRectangleNodes P p q e)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace s))
  continuous_toFun := by fun_prop
  source' := rfl
  target' := by
    change includeLaurent P p q (parameter _ _
      (ProjectionRectangleParameters.D BassH0Diagram.plusFace 1)) =
        includeLaurent P p q (parameter _ _
          (ProjectionRectangleParameters.L BassH0Diagram.plusFace 0))
    rw [Path.target, Path.source]

/-- S4 whole ordinary/shifted null words, retaining K.trans (L.trans cylinder) exactly.
Their starting points are compared by `positive_time_seam`; this is the pointwise whole
path equation, before any transport of path types or any unit/seed comparison. -/
theorem null_time_seam (e : Bool) (s : I) :
    ((firstNewPositive P p q e).trans (APath P p q e 1)) s =
      ((middleOldPositive P p q e).trans (middleNull P p q e)) s := by
  rcases Quillen.NativePathCells.cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [Quillen.NativePathCells.path_lower, Quillen.NativePathCells.path_lower]
    exact congrArg (includeLaurent P p q) (positive_time_seam P p q e t)
  · rw [Quillen.NativePathCells.path_upper, Quillen.NativePathCells.path_upper]
    exact (A_path P p q e 1 t).symm.trans (A_time_seam P p q e t)

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftConeSquares
