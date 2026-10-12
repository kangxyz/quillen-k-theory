/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.StableGeneralLinear

/-! Regression tests for the genuine finite-stage classifying-space factorization. -/

open CategoryTheory Quillen Quillen.StableGeneralLinear
open scoped Topology

universe u
variable {R S : Type u} [Ring R] [Ring S]

example {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, ClassifyingSpace (SingleObj (Quillen.StableGeneralLinear.Group R)))) :
    ∃ n, ∃ g : C(T, ClassifyingSpace (SingleObj (GL R n))),
      ∀ t, stageMap R n (g t) = f t := by
  obtain ⟨n, g, hg⟩ := compact_factors_original R f
  exact ⟨n, g, fun t => ContinuousMap.congr_fun hg t⟩

example (f : R →+* S) (n : ℕ) :
    classifyingSpaceMap (finiteMap f n).toFunctor ≫ stageMap S n =
      stageMap R n ≫ classifyingSpaceMap (map f).toFunctor := stageMap_ringMap R f n

example (n : ℕ) :
    classifyingSpaceMap (step R n).toFunctor ≫ stageMap R (n + 1) = stageMap R n := by
  have h := stageMap_transition R (Nat.le_succ n)
  have he : transition R n (n + 1) (Nat.le_succ n) = step R n := by
    apply MonoidHom.ext
    intro g
    exact transition_succ R n g
  simpa only [he] using h
