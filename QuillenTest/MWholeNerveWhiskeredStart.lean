/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskeredStart

/-! # Whole original component-face attachments, including the fixed half/quarter speeds -/
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
namespace QuillenTest.MWholeNerveWhiskeredStart
open BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The entire original first H1 component is the starting face of the target-whiskered cube. -/
theorem entire_postcomposed_attachment :
    ((cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
      (h0Anchor P (u ≫ v) w)).comp
      (⟨fun z : unitInterval × unitInterval ↦ ![1, lower z.1, z.2], by fun_prop⟩)) =
    (postcompLift P u v w).comp
      (⟨fun z : unitInterval × unitInterval ↦ ![0, z.1, z.2], by fun_prop⟩) := by
  apply ContinuousMap.ext
  intro z
  exact postcomp_start_face P u v w z.1 z.2

/-- The distinct original middle-quarter H1 component is the source-whiskered starting face. -/
theorem entire_precomposed_attachment :
    ((cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
      (rightStartingAnchor P u v w)).comp
      (⟨fun z : unitInterval × unitInterval ↦ ![1, upper z.1, upper (lower z.2)],
        by fun_prop⟩)) =
    (precompLift P u v w).comp
      (⟨fun z : unitInterval × unitInterval ↦ ![0, z.1, z.2], by fun_prop⟩) := by
  apply ContinuousMap.ext
  intro z
  exact precomp_start_face P u v w z.1 z.2

/-- The postcomposed attachment keeps the complete dependent reference, even for raw nodes. -/
theorem original_postcomposed_reference (i : Fin 31) :
    postcompNodes P u v w (h0Index i) =
      ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassH1References.firstNodes P (u ≫ v) w) i :=
  postcomp_start_nodes P u v w i

/-- The precomposed attachment likewise retains the actual reference after association. -/
theorem original_precomposed_reference (i : Fin 31) :
    precompNodes P u v w (h0Index i) =
      ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassH1References.middleNodes P u (v ≫ w)) i :=
  precomp_start_nodes P u v w i

end QuillenTest.MWholeNerveWhiskeredStart
