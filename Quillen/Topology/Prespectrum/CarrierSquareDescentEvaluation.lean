/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.CarrierSquareDescent
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-! Pointwise evaluation of quotient descent into the original native square. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.CarrierPathSquare
open LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {a₀ b₀ a₁ b₁ : X}
  {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}
  {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
  {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
  {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}

/-- A whole comparison image equation descends pointwise; no evaluator continuity is assumed. -/
theorem boundarySquare_native (J : p₀.Homotopy ((l.trans p₁).trans m.symm))
    (K : H₀.RelHomotopy ((L.trans H₁).trans M.symm))
    (n : ℕ) (x : E.space n) (ev : X → F.space n)
    (h : ∀ r s, ev (J (r, s)) = K.level n (r, (s, x)))
    (r s : unitInterval) :
    ev ((boundarySquare J).parameter (r, s)) = K.toSquare.level n (r, (s, x)) := by
  obtain ⟨z, hz⟩ := ThreeSideSquare.collapse_surjective (r, s)
  have hc := congrArg ev (boundaryParameter_collapse J z)
  change ev (boundaryParameter J (r, s)) = _
  rw [hz] at hc
  have hk := K.toSquare_collapse n z x
  rw [hz] at hk
  exact hc.trans ((h z.1 z.2).trans hk.symm)

end Quillen.CarrierPathSquare
