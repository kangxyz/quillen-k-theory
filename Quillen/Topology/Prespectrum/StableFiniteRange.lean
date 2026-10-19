/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StableConnectivity

/-!
# Stable equivalence from an eventual finite range at the original chosen points

Only the positive homotopy groups at the actual chosen points enter the original signed
stable systems. An eventual slope-two bijectivity range for those maps therefore suffices;
no connectivity assertion at arbitrary homotopy-fiber points is required. The arrow and
both prespectrum structures remain unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum

/-- Eventual finite bijectivity at the actual chosen points gives an original stable equivalence.
-/
theorem isStableEquivalence_of_eventually_linearPi {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (N c : ℕ) (hf : ∀ n, N ≤ n → ∀ k, k + 2 < 2 * n - c →
      Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
        (f.map (n + 1)) (f.map_point (n + 1)))) : IsStableEquivalence f := by
  intro d
  change IsIso (colimMap (stableSystemMap f d))
  apply sequentialColimitMap_isIso_of_eventually (stableSystemMap f d) (N + d.toNat + c + 1)
  intro n hn
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact hf ((-d).toNat + n + 1) (by omega) (d.toNat + n) (by omega)

end Quillen.LoopPrespectrum
