/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.WeakRelations

/-!
# The original weak-arrow track between canonical object loops

The two exact existing diagonal triangles are filled by their explicit convex realization
homotopies. Their original weak-arrow diagonal is the common intermediate path; neither a
chosen witness of path homotopy nor a K-zero relation replaces this two-parameter track.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B : C} (f : A ⟶ B) (hf : W.weq f)

/-- The actual upper triangle, with the source object followed by its original constant edge. -/
def weakObjectUpperTrack :
    ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)).Homotopy
      (realizationEdgePath (W.weakObjectEdge f hf)) := by
  exact (realizationEdgeCompositionHomotopy (W.weakObjectUpperCompStruct f hf)).cast
    (by rw [realizationEdgePath_id]; rfl) rfl

/-- The actual lower triangle, with its original constant edge followed by the target object. -/
def weakObjectLowerTrack :
    ((Path.refl W.kBasepoint).trans (W.kZeroObjectLoop B)).Homotopy
      (realizationEdgePath (W.weakObjectEdge f hf)) := by
  exact (realizationEdgeCompositionHomotopy (W.weakObjectLowerCompStruct f hf)).cast
    (by rw [realizationEdgePath_id]; rfl) rfl

/-- The specified weak-arrow track uses both original triangles and the standard unit tracks. -/
def weakObjectLoopTrack : (W.kZeroObjectLoop A).Homotopy (W.kZeroObjectLoop B) :=
  ((Path.Homotopy.transRefl (W.kZeroObjectLoop A)).symm.trans
    (W.weakObjectUpperTrack f hf)).trans
      (((Path.Homotopy.reflTrans (W.kZeroObjectLoop B)).symm.trans
        (W.weakObjectLowerTrack f hf)).symm)

/-- The first comparison face is the original source object loop at every loop parameter. -/
theorem weakObjectLoopTrack_zero (t : unitInterval) :
    W.weakObjectLoopTrack f hf (0, t) = W.kZeroObjectLoop A t :=
  (W.weakObjectLoopTrack f hf).apply_zero t

/-- The second comparison face is the original target object loop at every loop parameter. -/
theorem weakObjectLoopTrack_one (t : unitInterval) :
    W.weakObjectLoopTrack f hf (1, t) = W.kZeroObjectLoop B t :=
  (W.weakObjectLoopTrack f hf).apply_one t

/-- Independent comparison time preserves the original initial based endpoint. -/
theorem weakObjectLoopTrack_source (s : unitInterval) :
    W.weakObjectLoopTrack f hf (s, 0) = W.kBasepoint :=
  Path.Homotopy.source _ s

/-- Independent comparison time preserves the original final based endpoint. -/
theorem weakObjectLoopTrack_target (s : unitInterval) :
    W.weakObjectLoopTrack f hf (s, 1) = W.kBasepoint :=
  Path.Homotopy.target _ s

/-- The midpoint of the pasted track is exactly the original weak-arrow diagonal path. -/
theorem weakObjectLoopTrack_midpoint (t : unitInterval) :
    W.weakObjectLoopTrack f hf (⟨1 / 2, by norm_num, by norm_num⟩, t) =
      realizationEdgePath (W.weakObjectEdge f hf) t := by
  change (((Path.Homotopy.transRefl (W.kZeroObjectLoop A)).symm.trans
    (W.weakObjectUpperTrack f hf)).trans _)
      (⟨1 / 2, by norm_num, by norm_num⟩, t) = _
  rw [Path.Homotopy.trans_apply]
  simp only [le_refl, ↓reduceDIte]
  have h : (⟨2 * (1 / 2 : ℝ), by norm_num, by norm_num⟩ : unitInterval) = 1 := by
    apply Subtype.ext
    norm_num
  rw [h]
  exact (((Path.Homotopy.transRefl (W.kZeroObjectLoop A)).symm.trans
    (W.weakObjectUpperTrack f hf))).apply_one t

/-- A weak endomorphism gives the specified loop in the original object-loop component. -/
def weakEndomorphismLoop {A : C} (f : A ⟶ A) (hf : W.weq f) :
    Path (W.kZeroObjectLoop A) (W.kZeroObjectLoop A) where
  toFun s := (W.weakObjectLoopTrack f hf).eval s
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (W.weakObjectLoopTrack f hf).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The endomorphism loop retains independent weak-arrow and object-loop parameters. -/
theorem weakEndomorphismLoop_apply {A : C} (f : A ⟶ A) (hf : W.weq f)
    (s t : unitInterval) :
    W.weakEndomorphismLoop f hf s t = W.weakObjectLoopTrack f hf (s, t) := rfl

end Quillen.Waldhausen.Structure
