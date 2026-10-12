/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.LocalCoefficients.ChainSupport
import Quillen.Topology.LocalCoefficients.TelescopeHomologyElements
import Quillen.Topology.FilteredRealization.PathComponents

/-! Independent consumers of finite support, component control, and original stage maps. -/

noncomputable section
open CategoryTheory Limits Convexity Quillen Quillen.LocalCoefficients
open scoped Simplicial
universe u

example {X : Type u} [TopologicalSpace X] (A : System.{u, u} X) (n : ℕ)
    (x : homology A n) :
    ∃ s : Finset (SingularSimplex X ⦋n⦌), ∀ (B : System.{u, u} X) (η θ : A ⟶ B),
      (∀ σ ∈ s, η.app (FundamentalGroupoid.mk (σ (StdSimplex.single 0))) =
        θ.app (FundamentalGroupoid.mk (σ (StdSimplex.single 0)))) →
      coefficientHomologyMap η n x = coefficientHomologyMap θ n x :=
  homology_exists_finite_test_set A n x

example (F : ℕ ⥤ Cat.{u, u})
    (A : System.{u, u} (ClassifyingSpace (GrothendieckTelescope.Model F)))
    (k : ℕ) (x : homology A k) :
    ∃ (n : ℕ) (y : homology (pullback
      (classifyingSpaceMap (Grothendieck.ι F n)).hom A) k),
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k y = x :=
  GrothendieckTelescope.localHomology_exists_stage F A k x

example {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (j : J) (s : Finset |F.obj j|) :
    ∃ (k : J) (f : j ⟶ k), ∀ x ∈ s, ∀ y ∈ s,
      Joined (SSet.toTop.map (F.map f) x) (SSet.toTop.map (F.map f) y) ↔
        Joined (SSet.toTop.map (c.ι.app j) x) (SSet.toTop.map (c.ι.app j) y) :=
  FilteredRealization.finite_component_relations_stabilize F c hc j s
