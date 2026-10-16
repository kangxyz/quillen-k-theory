/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskeredTerminal

/-! # Exact original terminal component with full references and unchanged speeds -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveWhiskeredTerminal
open BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Equality is on the entire two-parameter face, at the two original different speeds. -/
theorem entire_original_terminal_attachment :
    (postcompLift P u v w).comp
      (⟨fun z : unitInterval × unitInterval ↦ ![1, upper z.1, upper (lower z.2)],
        by fun_prop⟩) =
    (precompLift P u v w).comp
      (⟨fun z : unitInterval × unitInterval ↦ ![1, lower z.1, z.2], by fun_prop⟩) := by
  apply ContinuousMap.ext
  intro z
  exact whiskered_terminal_face P u v w z.1 z.2

/-- Even repeated underlying functors retain their complete original dependent reference. -/
theorem entire_original_terminal_nodes (i : Fin 31) :
    postcompNodes P u v w (middleIndex i) = precompNodes P u v w (firstIndex i) :=
  whiskered_terminal_nodes P u v w i

/-- The anchor equation retains both the original geometric composition comparisons. -/
theorem original_terminal_reference_anchor :
    postcompAnchor P u v w ≪≫ CategoryTheory.Functor.isoWhiskerRight
        (BassH1References.middleIso P u v)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor =
      precompAnchor P u v w ≪≫ CategoryTheory.Functor.isoWhiskerLeft
        (coefficientModel P u).functor (BassH1References.firstIso P v w) :=
  whiskered_terminal_anchor P u v w

end QuillenTest.MWholeNerveWhiskeredTerminal
