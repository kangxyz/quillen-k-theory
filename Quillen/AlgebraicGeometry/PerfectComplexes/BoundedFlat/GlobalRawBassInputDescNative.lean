/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputDescSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputMap

/-!
# The full original raw input descent surface

The two unchanged geometric rectangle surfaces undergo the original common-outer-path
cancellation and the original ThreeSideSquare quotient. Every native point is retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputDescSimplex
open ProjectionRectangleParameters
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The whole positive projection rectangle retains both original geometric clocks. -/
theorem plus_rectangle_lift :
    HomotopyLift (simplex g) (rectangle BassH0Diagram.plusFace) (plusInputPasting g) := by
  intro n r s x
  exact (prespectrumSimplexFamily_face (simplex g) BassH0Diagram.plusFace n
    (DoubleSquareScalarPaths.rectangleParameter (r, s)) x).trans
    ((congrArg (fun S => prespectrumSimplexFamily S n
      (DoubleSquareScalarPaths.rectangleParameter (r, s), x)) (plus_face g)).trans
      (DoubleSquareScalarPaths.original_rectangle_nativeLift
        (projection.app Y) (plus.app Y) (projection.app X) (plus.app X)
        g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (plus.naturality g) n r s x))

/-- The inverse-coordinate rectangle retains its separate original normalization data. -/
theorem minus_rectangle_lift :
    HomotopyLift (simplex g) (rectangle BassH0Diagram.minusFace) (minusInputPasting g) := by
  intro n r s x
  exact (prespectrumSimplexFamily_face (simplex g) BassH0Diagram.minusFace n
    (DoubleSquareScalarPaths.rectangleParameter (r, s)) x).trans
    ((congrArg (fun S => prespectrumSimplexFamily S n
      (DoubleSquareScalarPaths.rectangleParameter (r, s), x)) (minus_face g)).trans
      (DoubleSquareScalarPaths.original_rectangle_nativeLift
        (projection.app Y) (minus.app Y) (projection.app X) (minus.app X)
        g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (minus.naturality g) n r s x))

/-- The complete original outer-track cancellation is evaluated without a replacement filler. -/
theorem boundary_native_lift :
    HomotopyLift (simplex g) BassH0Diagram.boundaryParameter (inputBoundary g) := by
  have jp := plus_rectangle_lift g
  have jm := minus_rectangle_lift g
  have sp := HomotopyLift.source (simplex g) jp
  have sm := HomotopyLift.source (simplex g) jm
  have tp := HomotopyLift.target (simplex g) jp
  have tm := HomotopyLift.target (simplex g) jm
  have lLp := PathLift.trans_left (simplex g) sp
  have lPp := PathLift.trans_right (simplex g) sp
  have lLm := PathLift.trans_left (simplex g) sm
  have lPm := PathLift.trans_right (simplex g) sm
  have lDp := PathLift.symm (simplex g) (PathLift.trans_left (simplex g) tp)
  have lDm := PathLift.symm (simplex g) (PathLift.trans_left (simplex g) tm)
  simp only [Path.symm_symm, Homotopy.symm_symm] at lDp lDm
  have lT := PathLift.trans_left (simplex g) (PathLift.trans_right (simplex g) tp)
  have lKp := PathLift.trans_right (simplex g) (PathLift.trans_right (simplex g) tp)
  have lKm := PathLift.trans_right (simplex g) (PathLift.trans_right (simplex g) tm)
  exact HomotopyLift.pasteProjectionSquares (simplex g)
    lDp lDm lT lLp lPp lKp lLm lPm lKm jp jm

/-- Both original endpoint transports preserve every point of the selected descent pasting. -/
theorem desc_native_lift :
    HomotopyLift (simplex g) BassH0Diagram.boundaryParameter (inputDescPasting g) := by
  intro n r s x
  exact boundary_native_lift g n r s x

/-- The selected quotient-collapse square retains the entire original input descent surface. -/
theorem square_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex g) n (BassH0Diagram.parameter (r, s), x) =
      (inputDescPasting g).toSquare.level n (r, (s, x)) :=
  HomotopyLift.toSquare (simplex g) (desc_native_lift g) n r s x

/-- The genuine comparison cylinder is the whole original two-chart quotient surface. -/
theorem cylinder_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    prespectrumSimplexFamily (simplex g) n (BassH0Diagram.parameter (r, s), x) =
      (inputComparisonHomotopy g).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Y))
          (boundedFlatPerfectPrespectrumMap (projection.app Y)) n (s, x)) :=
  (square_native g n r s x).trans (inputComparisonHomotopy_cylinder g n r s x).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputDescSimplex
