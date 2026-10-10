/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.EdgePathPresentation.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory

/-!
# The genuine fundamental groupoid on realized vertices

Every realization point can be joined to a vertex. Consequently the groupoid
whose objects are simplicial vertices and whose arrows are actual topological
path-homotopy classes is equivalent to the full fundamental groupoid.

The hom sets here are explicitly topological. This equivalence is not an
identification with the combinatorial groupoid completion; the remaining issue
is precisely the presentation of these hom sets by simplicial edges.
-/
@[expose] public section


noncomputable section

open CategoryTheory
open scoped Simplicial Topology

universe u v

namespace Quillen

/-- The full topological fundamental groupoid indexed by simplicial vertices. -/
def RealizationVertexGroupoid (X : SSet.{u}) :=
  InducedCategory (FundamentalGroupoid |X|)
    (fun x : X _⦋0⦌ ↦ FundamentalGroupoid.mk (realizationPoint x))

instance (X : SSet.{u}) : Groupoid (RealizationVertexGroupoid X) :=
  inferInstanceAs (Groupoid (InducedCategory _ _))

/-- Include the realized vertices, retaining all topological path classes
between them. -/
def realizationVertexInclusion (X : SSet.{u}) :
    RealizationVertexGroupoid X ⥤ FundamentalGroupoid |X| :=
  inducedFunctor _

instance (X : SSet.{u}) : (realizationVertexInclusion X).Full :=
  inferInstanceAs (Functor.Full (inducedFunctor _))

instance (X : SSet.{u}) : (realizationVertexInclusion X).Faithful :=
  inferInstanceAs (Functor.Faithful (inducedFunctor _))

/-- Realized vertices meet every component, including for a simplicial set
with no connectedness or nonemptiness assumption. -/
instance realizationVertexInclusion_essSurj (X : SSet.{u}) :
    (realizationVertexInclusion X).EssSurj where
  mem_essImage x := by
    obtain ⟨v, hv⟩ := realization_joined_vertex x.as
    exact ⟨v, ⟨(Groupoid.isoEquivHom (C := FundamentalGroupoid _) _ _).symm (show
      FundamentalGroupoid.mk (realizationPoint v) ⟶ x from
      ⟦hv.somePath⟧)⟩⟩

instance (X : SSet.{u}) : (realizationVertexInclusion X).IsEquivalence where

/-- Passing to vertices loses neither points up to isomorphism nor any
actual topological fundamental-groupoid morphisms. -/
def realizationVertexEquivalence (X : SSet.{u}) :
    RealizationVertexGroupoid X ≌ FundamentalGroupoid |X| :=
  (realizationVertexInclusion X).asEquivalence

/-- The canonical realized-arrow functor is essentially surjective for every
category. This assertion does not assert fullness or faithfulness. -/
instance classifyingFundamentalGroupoidFunctor_essSurj
    (C : Type u) [Category.{v} C] :
    (classifyingFundamentalGroupoidFunctor C).EssSurj where
  mem_essImage x := by
    obtain ⟨c, hc⟩ := classifyingSpace_joined_vertex x.as
    exact ⟨c, ⟨(Groupoid.isoEquivHom (C := FundamentalGroupoid _) _ _).symm (show
      FundamentalGroupoid.mk (classifyingSpacePoint c) ⟶ x from
      ⟦hc.somePath⟧)⟩⟩

end Quillen
