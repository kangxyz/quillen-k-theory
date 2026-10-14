/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MNativeOldFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MOldScalarEdges

/-! The actual 176 input nodes before common-order representative selection. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWhole
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Old family inputs come first, followed by the complete original first-stage M family. -/
def inputNode (i : Fin 176) : BassOverlap.Node P u v :=
  Fin.addCases (m := 131) (n := 45) (motive := fun _ ↦ BassOverlap.Node P u v)
    (BassH1Merged.nodes P u v) (BassMVertex.nodes P u v) i

/-- The input preserves every actual old full node without any new reference transport. -/
theorem input_old (i : Fin 131) :
    inputNode P u v (Fin.castAdd 45 i) = BassH1Merged.nodes P u v i := by
  unfold inputNode
  rw [Fin.addCases_left]

/-- The input preserves every actual first-stage full node without any reference change. -/
theorem input_vertex (i : Fin 45) :
    inputNode P u v (Fin.natAdd 131 i) = BassMVertex.nodes P u v i := by
  unfold inputNode
  rw [Fin.addCases_right]

/-- A previously proved full boundary node identity is retained as an actual input-node equality. -/
theorem input_boundary {i : Fin 45} {j : Fin 131}
    (h : BassMVertex.nodes P u v i = BassH1Merged.nodes P u v j) :
    inputNode P u v (Fin.natAdd 131 i) = inputNode P u v (Fin.castAdd 45 j) :=
  (input_vertex P u v i).trans (h.trans (input_old P u v j).symm)

end Quillen.PerfectComplexes.BassMWhole
