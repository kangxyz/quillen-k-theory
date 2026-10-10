/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremB.SequentialWeakCartesian

/-! # Weak finite-stage input, full-boundary HELP and actual sequential comparisons -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Topology Quillen Quillen.CartesianRealization.Sequential
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
  (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d)
  [∀ n, T1Space (F.obj n)] [∀ n, T1Space (G.obj n)]
  (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
  (hG : ∀ n, IsClosedEmbedding (G.map (homOfLE (Nat.le_succ n))))
  (k : ℕ) (hstage : ∀ n (h : k ≤ n), IsWeakHomotopyEquivalence (stageComparison η k n h))

example : IsWeakHomotopyEquivalence (colimitComparison η c hc d k) :=
  colimitComparison_isWeakHomotopyEquivalence_of_weakStages η c hc d hd hF hG k hstage
example : FiniteCubeStrictHELP (colimitComparison η c hc d k) :=
  colimitComparison_finiteCubeStrictHELP_of_weakStages η c hc d hd hF hG k hstage
example (a : C(CubicalTests.boundary.{u} 0,F.obj k))
    (b : C(CubicalTests.cube.{u} 0,ColimitPullback η c hc d k))
    (w : (colimitComparison η c hc d k).comp a = b.comp (CubicalTests.boundaryInclusion 0).hom) :
    ∃ l : C(CubicalTests.cube.{u} 0,F.obj k), l.comp (CubicalTests.boundaryInclusion 0).hom = a ∧
      Nonempty (((colimitComparison η c hc d k).comp l).HomotopyRel b
        (Set.range (CubicalTests.boundaryInclusion 0))) :=
  colimitComparison_finiteCubeStrictHELP_of_weakStages η c hc d hd hF hG k hstage 0 a b w
example (x : F.obj k) (t : unitInterval) :
    (colimitComparison η c hc d k x).val.2.2 t = d.ι.app k (η.app k x) := rfl
