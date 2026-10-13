/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.BarycentricGeometry
public import Mathlib.Data.List.FinRange

/-!
# Actual barycenters of finite vertex lists

The barycenter of a nonempty list is the uniform affine average of its vertices,
with repetitions retained. The empty augmentation list has an arbitrary fallback
which is never used by recursive coning.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Convexity

namespace Quillen.BarycentricSubdivision

variable {J K : Type*}

/-- Actual uniform barycenter of a nonempty list of simplex points. -/
def listBarycenter [Finite J] [Nonempty J] : List (StdSimplex ℝ J) → StdSimplex ℝ J
  | [] => StdSimplex.single (Classical.choice ‹Nonempty J›)
  | p :: l => tupleBarycenter (Fin.cons p (fun i : Fin l.length ↦ l[i.val]))

/-- Reindexing a uniform tuple by an equality of lengths preserves its average. -/
theorem tupleBarycenter_cast [Finite J] {m n : ℕ} (h : m = n)
    (v : Fin (m + 1) → StdSimplex ℝ J) :
    tupleBarycenter v = tupleBarycenter
      (fun i : Fin (n + 1) ↦ v (Fin.cast (congrArg (fun k ↦ k + 1) h.symm) i)) := by
  subst n
  rfl

/-- The list barycenter is natural for every affine map, with no restriction on
repeated vertices. -/
theorem listBarycenter_natural [Finite J] [Nonempty J] [Finite K] [Nonempty K]
    (l : List (StdSimplex ℝ J)) (hl : l ≠ [])
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ J) (StdSimplex ℝ K)) :
    f (listBarycenter l) = listBarycenter (l.map f) := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons p l =>
    simp only [listBarycenter, List.map_cons]
    rw [tupleBarycenter_natural]
    rw [tupleBarycenter_cast (List.length_map (as := l) f).symm]
    apply congrArg (fun v : Fin ((l.map f).length + 1) → StdSimplex ℝ K ↦ tupleBarycenter v)
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp only [Fin.cast_succ_eq, Function.comp_apply, Fin.cons_succ, List.getElem_map,
        Fin.val_cast]

end Quillen.BarycentricSubdivision
