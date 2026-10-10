/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.QuillenComparison.IntervalSpans
public import Quillen.Topology.Realization.Edgewise
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The nested central intervals of edgewise subdivision

The i-th interval is [n-i,n+1+i] in [2n+1]. Its nerve index is n+1+i.
These choices are natural for the genuine reversed-first-half edgewise functor.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite
open scoped Simplicial CategoryTheory.Prod

namespace Quillen.Waldhausen.QuillenComparison

/-- The left endpoint of the central nested interval. -/
def lowerIndex (n : SimplexCategory) (i : Fin (n.len + 1)) :
    Fin ((Edgewise.ε.obj n).len + 1) :=
  (Edgewise.left n n).toOrderHom i.rev

/-- The right endpoint, also used in the original nerve direction. -/
def upperIndex (n : SimplexCategory) (i : Fin (n.len + 1)) :
    Fin ((Edgewise.ε.obj n).len + 1) :=
  (Edgewise.right n n).toOrderHom i

theorem lowerIndex_le_upperIndex (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    lowerIndex n i ≤ upperIndex n j := by
  change i.rev.val ≤ n.len + 1 + j.val
  have := i.rev.isLt
  omega

theorem lowerIndex_antitone (n : SimplexCategory) : Antitone (lowerIndex n) := by
  intro i j hij
  exact (Edgewise.left n n).toOrderHom.monotone (Fin.rev_le_rev.mpr hij)

theorem upperIndex_monotone (n : SimplexCategory) : Monotone (upperIndex n) :=
  (Edgewise.right n n).toOrderHom.monotone

@[simp]
theorem lowerIndex_naturality {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (Edgewise.ε.map f).toOrderHom (lowerIndex n i) = lowerIndex m (f.toOrderHom i) := by
  dsimp only [Edgewise.ε, lowerIndex]
  rw [Edgewise.joinMap_left]
  simp [SimplexCategory.rev_map_apply]

@[simp]
theorem upperIndex_naturality {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (Edgewise.ε.map f).toOrderHom (upperIndex n i) = upperIndex m (f.toOrderHom i) :=
  Edgewise.joinMap_right (SimplexCategory.rev.map f) f i

/-- The central intervals, ordered by containment. -/
def centralInterval (n : SimplexCategory) (i : Fin (n.len + 1)) :
    NestedInterval (Edgewise.ε.obj n) :=
  ⟨(OrderDual.toDual (lowerIndex n i), upperIndex n i), lowerIndex_le_upperIndex n i i⟩

/-- The two indexing directions used by the diagonal comparison. -/
def comparisonIndices (n : SimplexCategory) :
    Fin (n.len + 1) ⥤ Fin ((Edgewise.ε.obj n).len + 1) × NestedInterval (Edgewise.ε.obj n) where
  obj i := (upperIndex n i, centralInterval n i)
  map {i j} f :=
    (homOfLE (upperIndex_monotone n (leOfHom f)),
      homOfLE (show centralInterval n i ≤ centralInterval n j from
        ⟨lowerIndex_antitone n (leOfHom f), upperIndex_monotone n (leOfHom f)⟩))
  map_id _ := by ext <;> apply Subsingleton.elim
  map_comp _ _ := by ext <;> apply Subsingleton.elim

end Quillen.Waldhausen.QuillenComparison
