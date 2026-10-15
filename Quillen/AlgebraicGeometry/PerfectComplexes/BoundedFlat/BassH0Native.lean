/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleParameters

/-! The whole original H0 cylinder face, with every native pasting and collapse retained. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Diagram
open ProjectionRectangleParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

/-- The full positive native projection comparison lifts through its exact scalar face. -/
theorem plus_rectangle_lift : HomotopyLift (simplex P w) (rectangle plusFace)
    (boundedFlatCoefficientPlusPasting P w) := by
  intro n r s x
  exact plus_native P w n r s x

/-- The full inverse projection comparison lifts through its separate exact scalar face. -/
theorem minus_rectangle_lift : HomotopyLift (simplex P w) (rectangle minusFace)
    (boundedFlatCoefficientMinusPasting P w) := by
  intro n r s x
  exact minus_native P w n r s x

/-- The literal original Bass boundary, including cancellation of the common outer track. -/
theorem boundary_native_lift : HomotopyLift (simplex P w) boundaryParameter
    (boundedFlatCoefficientBassBoundary P w) := by
  have jp := plus_rectangle_lift P w
  have jm := minus_rectangle_lift P w
  have sp := HomotopyLift.source (simplex P w) jp
  have sm := HomotopyLift.source (simplex P w) jm
  have tp := HomotopyLift.target (simplex P w) jp
  have tm := HomotopyLift.target (simplex P w) jm
  have lLp := PathLift.trans_left (simplex P w) sp
  have lPp := PathLift.trans_right (simplex P w) sp
  have lLm := PathLift.trans_left (simplex P w) sm
  have lPm := PathLift.trans_right (simplex P w) sm
  have lDp := PathLift.symm (simplex P w) (PathLift.trans_left (simplex P w) tp)
  have lDm := PathLift.symm (simplex P w) (PathLift.trans_left (simplex P w) tm)
  simp only [Path.symm_symm, Homotopy.symm_symm] at lDp lDm
  have lT := PathLift.trans_left (simplex P w) (PathLift.trans_right (simplex P w) tp)
  have lKp := PathLift.trans_right (simplex P w) (PathLift.trans_right (simplex P w) tp)
  have lKm := PathLift.trans_right (simplex P w) (PathLift.trans_right (simplex P w) tm)
  exact HomotopyLift.pasteProjectionSquares (simplex P w)
    lDp lDm lT lLp lPp lKp lLm lPm lKm jp jm

/-- Both original ofLevels transports preserve the complete boundary family. -/
theorem desc_native_lift : HomotopyLift (simplex P w) boundaryParameter
    (boundedFlatCoefficientBassDescPasting P w) := by
  intro n r s x
  exact boundary_native_lift P w n r s x

/-- Every point of the original comparison homotopy on every original cylinder input. -/
theorem native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P w) n (parameter (s, t), x) =
      (boundedFlatCoefficientBassComparisonHomotopy P w).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [boundedFlatCoefficientBassComparisonHomotopy_cylinder]
  exact HomotopyLift.toSquare (simplex P w) (desc_native_lift P w) n s t x

/-- The exact required H0 face of the original composition cube, with both times independent. -/
theorem composition_H0 {c : Under R} (u : a ⟶ b) (v : b ⟶ c)
    (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P (u ≫ v)) n (parameter (s, t), x) =
      (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  native P (u ≫ v) n s t x

/-- The entire actual H0 family fixes the original point. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 31)) :
    prespectrumSimplexFamily (simplex P w) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj b)))).point n :=
  prespectrumSimplexFamily_point (simplex P w) n z

/-- The structure time remains separate from both H0 coordinates and all scalar parameters. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 31))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P w) (n + 1)
      (z, (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj b)))).structureMap n
        (prespectrumSimplexFamily (simplex P w) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P w) n z x t

end Quillen.PerfectComplexes.BassH0Diagram
