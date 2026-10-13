/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Realization.RelativeSphericalStraightening
import Quillen.Topology.LocalCoefficients.RelativeFiniteBoundary

/-! # Independent H0-to-H4 finite-boundary consumer -/

noncomputable section

open CategoryTheory Limits Quillen Quillen.LocalCoefficients Convexity
open scoped Simplicial

universe u

variable {Z : Type u} [TopologicalSpace Z] [PathConnectedSpace Z]

/-- An actual zero relative cycle supplies a finite boundary support, and that
very support admits complete face-compatible relative spherical straightening.
The original coefficient fibers and categorical boundary equation are retained. -/
example (n : ℕ) (z : Z) (f₀ : SphericalSimplex Z z n)
    (W : Set Z) (A : System.{u, u} Z)
    (c : (relativeSingularChainComplex W A).cycles n)
    (hc : (relativeSingularChainComplex W A).homologyπ n c = 0)
    (hs : ∀ x : Z, ∀ k : ℕ, 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k Z x)) :
    ∃ (b : Finset (SingularSimplex Z ⦋n + 1⦌)) (a : ∀ τ, simplexFiber A τ),
      (relativeSingularChainComplex W A).d (n + 1) n
        ((cokernel.π (pushforwardChainMap (subspaceInclusion W) A)).f (n + 1)
          (∑ τ ∈ b, chainInclusion A τ (a τ))) =
        (relativeSingularChainComplex W A).iCycles n c ∧
      Nonempty (PartialSimplexStraightening n z (sphericalStraighteningFamily f₀ b)
        (sphericalStraighteningFixedFamily f₀) (sphericalStraighteningFamily_faceClosed f₀ b)
        (n + 2)) := by
  obtain ⟨b, a, hb⟩ := relativeCycle_exists_finite_boundary W A n c hc
  exact ⟨b, a, hb, exists_relative_spherical_straightening n z f₀ b hs⟩

/-- Any top simplex produced by that family has the genuine geometric skeleton
at the basepoint; the two highest dimensions need no extra Pi vanishing. -/
example {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}
    (P : PartialSimplexStraightening n z S F hS N) (hd : n + 1 < N)
    (s : {s // s ∈ S (n + 1)}) (x : StdSimplex ℝ (Fin (n + 2)))
    (hx : x.weights.support.card ≤ n) :
    P.endpoint (n + 1) s x = z := P.endpoint_skeleton (n + 1) hd s x hx
