/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.EdgePathPresentation.CellPathGeneration

/-! A consumer of cell-path generation after an arbitrary ambient continuous map. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Topology
universe u
namespace QuillenTest.CellPathGeneration

open Quillen

/-- Membership of all old-space and cell paths can be checked after an arbitrary
continuous map out of the genuine attachment; every continuous path then has it. -/
theorem mapped_attachment_path_mem (X : TopCat.{u}) [DiscreteTopology X] (n : ℕ)
    {C D Y : TopCat.{u}} {f : TopCat.of (X × simplexBoundary n) ⟶ C}
    {g : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : C ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X n) f g j)
    (h : C(D, Y)) (S : Subgroupoid (FundamentalGroupoid Y))
    (hold : ∀ {x y : C} (p : Path x y),
      (⟦p.map (h.comp j.hom).continuous⟧ : FundamentalGroupoid.mk (h (j x)) ⟶
        FundamentalGroupoid.mk (h (j y))) ∈ S.arrows _ _)
    (hcell : ∀ (a : X) {x y : StdSimplex ℝ (Fin (n + 1))} (p : Path x y),
      (⟦p.map (h.comp (simplexAttachmentCellMap X n (g := g) a)).continuous⟧ :
        FundamentalGroupoid.mk (h (g (a, x))) ⟶
          FundamentalGroupoid.mk (h (g (a, y)))) ∈ S.arrows _ _)
    {x y : D} (p : Path x y) :
    (⟦p.map h.continuous⟧ : FundamentalGroupoid.mk (h x) ⟶
      FundamentalGroupoid.mk (h y)) ∈ S.arrows _ _ := by
  let T := S.comap (FundamentalGroupoid.map h)
  have hT : T = ⊤ := simplexAttachment_subgroupoid_eq_top X n sq T
    (fun {_ _} p ↦ hold p) (fun a {_ _} p ↦ hcell a p)
  have hp : (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ T.arrows _ _ := by
    rw [hT]
    trivial
  exact hp

end QuillenTest.CellPathGeneration
