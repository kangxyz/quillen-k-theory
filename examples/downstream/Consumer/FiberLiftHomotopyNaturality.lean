/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.FiberLiftHomotopyNaturality

/-!
# Stable localization transport through a specified whole null square

This independent client transports stability from one original specified fiber lift and
simultaneously retains its signed connecting map in every integer degree. The whole null
square remains an explicit input, to be constructed by any geometric application.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum

universe u

namespace Consumer.FiberLiftHomotopyNaturality

/-- One stable same-null lift and three stable comparisons give a stable target lift together
with naturality of the original signed boundary in every integer degree. -/
theorem transport_stable_lift_and_boundary
    {S A O S' A' O' : LoopPrespectrum.{u}}
    (f : S ⟶ A) (r : A ⟶ O) (f' : S' ⟶ A') (r' : A' ⟶ O')
    (N : LoopPrespectrum.Homotopy (f ≫ r) (zeroHom S O))
    (N' : LoopPrespectrum.Homotopy (f' ≫ r') (zeroHom S' O'))
    (s : S ⟶ S') (a : A ⟶ A') (o : O ⟶ O')
    (Hf : LoopPrespectrum.Homotopy (f ≫ a) (s ≫ f'))
    (Hr : LoopPrespectrum.Homotopy (a ≫ r') (r ≫ o))
    (Q : (homotopyFiberLiftSquareNullHomotopy f r r' N a o Hr).Square
      (homotopyFiberLiftTargetNullHomotopy f' r' N' s)
      (Hf.postcomp r') (LoopPrespectrum.Homotopy.refl (zeroHom S O')))
    (hs : IsStableEquivalence s) (ha : IsStableEquivalence a)
    (ho : IsStableEquivalence o) (h : IsStableEquivalence (homotopyFiberLift r f N)) :
    ∃ h' : IsStableEquivalence (homotopyFiberLift r' f' N'), ∀ d : ℤ,
      letI := h d
      letI := h' d
      stableFiberLiftConnecting f r N d ≫ (stableHomotopyFunctor d).map s =
        (stableHomotopyFunctor (d + 1)).map o ≫ stableFiberLiftConnecting f' r' N' d := by
  let h' := (homotopyFiberLift_homotopySquare_isStableEquivalence_iff
    f r f' r' N N' s a o Hf Hr Q hs ha ho).mp h
  refine ⟨h', ?_⟩
  intro d
  let := h d
  let := h' d
  exact stableFiberLiftConnecting_homotopySquare f r f' r' N N' s a o Hf Hr Q d

end Consumer.FiberLiftHomotopyNaturality
