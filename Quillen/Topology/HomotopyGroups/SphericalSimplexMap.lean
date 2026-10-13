/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.SphericalSimplex
public import Quillen.Topology.HomotopyGroups.Map

/-!
# Original-map naturality of spherical singular-simplex classes

Postcomposition retains the actual continuous map and the specified equality
of basepoints. The chosen simplex-to-cube class map commutes with the existing
homotopyGroupMap by a literal equality on representatives.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Convexity
universe u v

namespace Quillen.SphericalSimplex
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y} {n : ℕ}

/-- Postcompose an actual spherical simplex by a based continuous map. -/
def map (f : C(X, Y)) (h : f x = y) (σ : SphericalSimplex X x n) :
    SphericalSimplex Y y n :=
  ⟨f.comp σ.val, fun t ht ↦ (congrArg f (σ.boundary t ht)).trans h⟩

@[simp] theorem map_apply (f : C(X, Y)) (h : f x = y)
    (σ : SphericalSimplex X x n) (t : StdSimplex ℝ (Fin (n + 1))) :
    map f h σ t = f (σ t) := rfl

/-- The representative in the original cube model commutes with postcomposition. -/
@[simp] theorem toGenLoop_map (f : C(X, Y)) (h : f x = y)
    (σ : SphericalSimplex X x n) :
    (map f h σ).toGenLoop = genLoopPostcomp f h σ.toGenLoop := rfl

/-- The class equation uses the original homotopy map, including its endpoint equality. -/
@[simp] theorem homotopyClass_map (f : C(X, Y)) (h : f x = y)
    (σ : SphericalSimplex X x n) :
    (map f h σ).homotopyClass = homotopyGroupMap f h σ.homotopyClass := rfl

end Quillen.SphericalSimplex
