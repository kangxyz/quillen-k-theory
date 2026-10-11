/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyGroups.PathTransport

/-!
# Endpoint-aware naturality and actual squares of basepoint transport

The original path transport is natural for a continuous map with displayed endpoint equalities.
A whole continuous square gives the exact commuting square of the four original transports, in
all finite degrees. Its proof uses actual free-path evaluation maps, without a path-connectedness
hypothesis or an assumed composition law for basepoint transport.
-/

@[expose] public section

noncomputable section

open scoped Topology unitInterval

universe u v

namespace Quillen

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Naturality retains displayed endpoint identifications and the whole original track. -/
theorem pathTransport_naturality_of_track
    {a b : X} {c d : Y} (f : C(X, Y)) (γ : Path a b) (δ : Path c d)
    (h₀ : f a = c) (h₁ : f b = d) (htrack : ∀ t, f (γ t) = δ t)
    (n : ℕ) (α : HomotopyGroup.Pi n X a) :
    pathTransport δ n (homotopyGroupMap f h₀ α) =
      homotopyGroupMap f h₁ (pathTransport γ n α) := by
  subst c
  subst d
  have he : δ = γ.map f.continuous := by ext t; exact (htrack t).symm
  subst δ
  exact pathTransport_naturality f γ n α

/-- The four original edge transports commute around an actual continuous square. -/
theorem pathTransport_square {a₀ a₁ b₀ b₁ : X}
    (p : Path a₀ a₁) (q : Path b₀ b₁) (r : Path a₀ b₀) (s : Path a₁ b₁)
    (H : C(unitInterval × unitInterval, X))
    (h₀ : ∀ t, H (0, t) = p t) (h₁ : ∀ t, H (1, t) = q t)
    (hleft : ∀ t, H (t, 0) = r t) (hright : ∀ t, H (t, 1) = s t)
    (n : ℕ) (a : HomotopyGroup.Pi n X a₀) :
    pathTransport q n (pathTransport r n a) = pathTransport s n (pathTransport p n a) := by
  let L : Path p.toContinuousMap q.toContinuousMap :=
    { toFun t := ⟨fun z ↦ H (t, z), by fun_prop⟩
      continuous_toFun := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact H.continuous
      source' := by ext t; exact h₀ t
      target' := by ext t; exact h₁ t }
  obtain ⟨b, hb⟩ := (pathStartEquiv p n).surjective a
  change homotopyGroupMap (freePathEvaluation X 0) p.source b = a at hb
  have hl := pathTransport_naturality_of_track (freePathEvaluation X 0) L r
    p.source q.source hleft n b
  have hr := pathTransport_naturality_of_track (freePathEvaluation X 1) L s
    p.target q.target hright n b
  calc
    pathTransport q n (pathTransport r n a) =
        pathTransport q n (homotopyGroupMap (freePathEvaluation X 0) q.source
          (pathTransport L n b)) := congrArg (pathTransport q n)
            ((congrArg (pathTransport r n) hb.symm).trans hl)
    _ = homotopyGroupMap (freePathEvaluation X 1) q.target (pathTransport L n b) :=
      pathTransport_homotopyGroupMap_start q n _
    _ = pathTransport s n (homotopyGroupMap (freePathEvaluation X 1) p.target b) := hr.symm
    _ = pathTransport s n (pathTransport p n a) := congrArg (pathTransport s n)
      ((pathTransport_homotopyGroupMap_start p n b).symm.trans
        (congrArg (pathTransport p n) hb))

end Quillen
