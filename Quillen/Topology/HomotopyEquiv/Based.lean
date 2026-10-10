/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyGroups.Map

/-! # Based homotopy equivalences induce actual homotopy-group isomorphisms -/
@[expose] public section


noncomputable section
universe u v
open unitInterval

namespace Quillen
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homotopy equivalence with explicit basepoints and inverse homotopies
that remain fixed at those basepoints. These are standard geometric data. -/
structure BasedHomotopyEquiv (x : X) (y : Y) where
  /-- The forward continuous map from `X` to `Y`. -/
  toMap : C(X, Y)
  /-- The inverse continuous map from `Y` to `X`. -/
  invMap : C(Y, X)
  /-- The forward map carries the chosen point `x` to `y`. -/
  map_point : toMap x = y
  /-- The inverse map carries the chosen point `y` to `x`. -/
  inv_point : invMap y = x
  /-- A specified homotopy from the inverse-after-forward composite to the identity on `X`. -/
  leftHomotopy : (invMap.comp toMap).Homotopy (ContinuousMap.id X)
  /-- A specified homotopy from the forward-after-inverse composite to the identity on `Y`. -/
  rightHomotopy : (toMap.comp invMap).Homotopy (ContinuousMap.id Y)
  /-- The left inverse homotopy fixes `x` at every time. -/
  left_fixed : ∀ t : I, leftHomotopy (t, x) = x
  /-- The right inverse homotopy fixes `y` at every time. -/
  right_fixed : ∀ t : I, rightHomotopy (t, y) = y

namespace BasedHomotopyEquiv
variable {x : X} {y : Y} (e : BasedHomotopyEquiv x y)

/-- The induced equivalence of homotopy sets for any cube index type,
including the empty index which gives connected components. -/
def homotopySetEquiv (N : Type*) : HomotopyGroup N X x ≃ HomotopyGroup N Y y where
  toFun := homotopyGroupMap e.toMap e.map_point
  invFun := homotopyGroupMap e.invMap e.inv_point
  left_inv a := by
    rw [← homotopyGroupMap_comp]
    have hh := homotopyGroupMap_eq_of_based_homotopy (N := N)
      (f := e.invMap.comp e.toMap) (g := ContinuousMap.id X) (x := x) (y := x)
      ((congrArg e.invMap e.map_point).trans e.inv_point) rfl
      e.leftHomotopy e.left_fixed
    exact (congrFun hh a).trans (homotopyGroupMap_id a)
  right_inv a := by
    rw [← homotopyGroupMap_comp]
    have hh := homotopyGroupMap_eq_of_based_homotopy (N := N)
      (f := e.toMap.comp e.invMap) (g := ContinuousMap.id Y) (x := y) (y := y)
      ((congrArg e.toMap e.inv_point).trans e.map_point) rfl
      e.rightHomotopy e.right_fixed
    exact (congrFun hh a).trans (homotopyGroupMap_id a)

lemma piMap_leftInverse (n : ℕ) :
    (piMap n e.invMap e.inv_point).comp (piMap n e.toMap e.map_point) =
      MonoidHom.id (HomotopyGroup.Pi (n + 1) X x) := by
  rw [← homotopyGroupMapHom_comp]
  exact (piMap_eq_of_based_homotopy n _ rfl e.leftHomotopy e.left_fixed).trans
    homotopyGroupMapHom_id

lemma piMap_rightInverse (n : ℕ) :
    (piMap n e.toMap e.map_point).comp (piMap n e.invMap e.inv_point) =
      MonoidHom.id (HomotopyGroup.Pi (n + 1) Y y) := by
  rw [← homotopyGroupMapHom_comp]
  exact (piMap_eq_of_based_homotopy n _ rfl e.rightHomotopy e.right_fixed).trans
    homotopyGroupMapHom_id

/-- The induced isomorphism of positive-dimensional homotopy groups. -/
def piEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x ≃* HomotopyGroup.Pi (n + 1) Y y where
  toFun := piMap n e.toMap e.map_point
  invFun := piMap n e.invMap e.inv_point
  left_inv a := congrArg (fun k : HomotopyGroup.Pi (n + 1) X x →*
    HomotopyGroup.Pi (n + 1) X x => k a) (e.piMap_leftInverse n)
  right_inv a := congrArg (fun k : HomotopyGroup.Pi (n + 1) Y y →*
    HomotopyGroup.Pi (n + 1) Y y => k a) (e.piMap_rightInverse n)
  map_mul' := (piMap n e.toMap e.map_point).map_mul

end BasedHomotopyEquiv
end Quillen
