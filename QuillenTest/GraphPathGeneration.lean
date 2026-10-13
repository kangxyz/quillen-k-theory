/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.EdgePathPresentation.GraphPathGeneration

/-!
# Unique original representatives of actual graph paths

For a discrete family of geometric intervals attached to a discrete vertex
space, compatibility on the original vertices and whole edges suffices to
represent every continuous path by a morphism of the original groupoid.
The path may traverse infinitely many portions of edges before subdivision;
no edge-path approximation is assumed in the theorem.
-/
@[expose] public section

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Convexity Topology Set
open scoped Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace QuillenTest.GraphPathGeneration

open Quillen
open GraphAttachment

variable (X : TopCat.{u}) [DiscreteTopology X] {V D Y : TopCat.{u}}
    [DiscreteTopology V]
    {f : TopCat.of (X × simplexBoundary 1) ⟶ V}
    {g : TopCat.of (X × StdSimplex ℝ (Fin 2)) ⟶ D} {j : V ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X 1) f g j)
    (h : C(D, Y)) {A : Type v} [Groupoid.{w} A]
    (F : A ⥤ FundamentalGroupoid Y) (vertex : V → A)
    (ε : ∀ c : V, F.obj (vertex c) ≅ FundamentalGroupoid.mk (h (j c)))
    (edge : ∀ a : X, vertex (f (a, boundaryZero)) ⟶ vertex (f (a, boundaryOne)))
    (hedge : ∀ a : X, spoke X sq h F vertex ε a (StdSimplex.single 1) =
      F.map (edge a) ≫ (vertexIso X sq h F vertex ε a boundaryOne).hom)

include hedge in
/-- When the original groupoid representation is faithful, a genuine graph path
has a unique original arrow representative with the specified vertex transport. -/
theorem unique_original_representative [F.Faithful] {c d : V}
    (p : Path (j c) (j d)) :
    ∃! q : vertex c ⟶ vertex d,
      F.map q = (ε c).hom ≫
        (⟦p.map h.continuous⟧ : FundamentalGroupoid.mk (h (j c)) ⟶
          FundamentalGroupoid.mk (h (j d))) ≫ (ε d).inv := by
  obtain ⟨q, hq⟩ := path_from_original_edges X sq h F vertex ε edge hedge p
  exact ⟨q, hq, fun r hr ↦ F.map_injective (hr.trans hq.symm)⟩

end QuillenTest.GraphPathGeneration
