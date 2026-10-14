/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceBoundaryScalars

/-! Every literal second-stage scalar value remains on the original whole H1 target path. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity Quillen.ParameterSupport
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMReassociation

/-- The actual fixed H1 target path, retaining its original parameterization and all its values. -/
def targetRange : Set (StdSimplex ℝ (Fin 131)) :=
  Set.range (fun t : unitInterval ↦ BassH1Order.h1Parameter.{u} (1, t))

/-- The complete original five-piece source word lies in that exact target path range. -/
theorem word_in : PathIn targetRange.{u}
    (Ppath.trans ((Qpath.trans (Tpath.trans Upath)).trans Vpath)) :=
  fun t ↦ ⟨t, h1_target_word t⟩

/-- Each native associator resamples the supplied paths, preserving the whole original range. -/
theorem reassociation_in : HomotopyIn targetRange.{u} reassociation := by
  have hP := path_trans_left word_in.{u}
  have hrest := path_trans_right word_in.{u}
  have hQTU := path_trans_left hrest
  have hV := path_trans_right hrest
  have hQ := path_trans_left hQTU
  have hTU := path_trans_right hQTU
  have hT := path_trans_left hTU
  have hU := path_trans_right hTU
  exact hom_trans (hom_hcomp (hom_refl hP)
    (hom_transAssoc hQ (path_trans hT hU) hV))
    (hom_trans (hom_hcomp (hom_refl hP) (hom_hcomp (hom_refl hQ) (hom_transAssoc hT hU hV)))
      (hom_symm (hom_transAssoc hP hQ (path_trans hT (path_trans hU hV)))))

/-- Every second-stage point is an actual value of the unchanged original H1 target path. -/
theorem second_in_h1_target (r t : unitInterval) :
    ∃ s : unitInterval, BassH1Order.h1Parameter.{u} (1, s) = secondParameter (r, t) :=
  (hom_symm reassociation_in.{u}) (r, t)

end Quillen.PerfectComplexes.BassMReassociation
