/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ZigzagSequentializationNaturality
public import Quillen.Topology.Prespectrum.ZigzagSequentializationLinearGrowth
public import Quillen.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# Actual target replacements of a canonical zigzag sequentialization

Strict maps on the original zigzag vertices give actual finite-pushout and telescope maps.
Stability of the original comparison arrows detects their stability by the strict comparison
squares. In particular an actual target replacement sends both original legs to their literal
postcomposites. A factorization homotopy available only after such a replacement can be used
there without asserting an unstabilized homotopy or converting a localized equality to one.

The comparison-arrow stability premises are discharged by the preceding finite-growth theory;
no functoriality of homotopy pushouts in a localized category is assumed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (E' V' : ℕ → LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)
    (d : ∀ n, E n ⟶ E' n) (v : ∀ n, V n ⟶ V' n)
    (ha : ∀ n, a n ≫ v n = d n ≫ a' n)
    (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b' n)
    (hq : ∀ n, IsStableEquivalence (comparison E V a b n))
    (hq' : ∀ n, IsStableEquivalence (comparison E' V' a' b' n))
    (hd : ∀ n, IsStableEquivalence (d n))

include hq hq' hd in
/-- Genuine stable comparison arrows detect the same original recursive stage map. -/
theorem stageMap_isStableEquivalence (n : ℕ) :
    IsStableEquivalence (stageMap E V a b E' V' a' b' d v ha hb n) := by
  intro k
  let := hq n k
  let := hq' n k
  let := hd n k
  have h := congrArg ((stableHomotopyFunctor k).map)
    (comparison_naturality E V a b E' V' a' b' d v ha hb n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have : IsIso ((stableHomotopyFunctor k).map (comparison E V a b n) ≫
      (stableHomotopyFunctor k).map (stageMap E V a b E' V' a' b' d v ha hb n)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((stableHomotopyFunctor k).map (comparison E V a b n)) _

variable [∀ n k, T1Space ((E n).space k)] [∀ n k, T1Space ((V n).space k)]
    [∀ n k, T1Space ((E' n).space k)] [∀ n k, T1Space ((V' n).space k)]

include hq hq' hd in
/-- These actual strict stage maps give a stable equivalence of the original telescopes. -/
theorem inducedTelescopeMap_isStableEquivalence :
    IsStableEquivalence (inducedTelescopeMap E V a b E' V' a' b' d v ha hb) := by
  let : ∀ n k, T1Space ((stage E V a b n).space k) := stageSpaceT1Space E V a b
  let : ∀ n k, T1Space ((stage E' V' a' b' n).space k) := stageSpaceT1Space E' V' a' b'
  exact Telescope.map_isStableEquivalence _ _ _ _ _ _
    (stageMap_isStableEquivalence E V a b E' V' a' b' d v ha hb hq hq' hd)

section TargetReplacement
variable (W : ℕ → LoopPrespectrum.{u}) (s : ∀ n, V n ⟶ W n)

/-- An actual target map replaces both original legs by their literal postcomposites. -/
def targetReplacementMap :
    Telescope.prespectrum (stage E V a b) (transition E V a b) ⟶
      Telescope.prespectrum (stage E W (fun n ↦ a n ≫ s n) (fun n ↦ b n ≫ s n))
        (transition E W (fun n ↦ a n ≫ s n) (fun n ↦ b n ≫ s n)) :=
  inducedTelescopeMap E V a b E W (fun n ↦ a n ≫ s n) (fun n ↦ b n ≫ s n)
    (fun n ↦ 𝟙 (E n)) s (fun n ↦ by simp) (fun n ↦ by simp)

variable [∀ n k, T1Space ((W n).space k)]

include hq in
/-- Genuine stable comparison arrows on both sides make this exact target replacement stable. -/
theorem targetReplacementMap_isStableEquivalence
    (hqs : ∀ n, IsStableEquivalence
      (comparison E W (fun n ↦ a n ≫ s n) (fun n ↦ b n ≫ s n) n)) :
    IsStableEquivalence (targetReplacementMap E V a b W s) :=
  inducedTelescopeMap_isStableEquivalence E V a b E W
    (fun n ↦ a n ≫ s n) (fun n ↦ b n ≫ s n) (fun n ↦ 𝟙 (E n)) s
    (fun n ↦ by simp) (fun n ↦ by simp) hq hqs (fun n ↦ IsStableEquivalence.id (E n))

end TargetReplacement
end Quillen.LoopPrespectrum.ZigzagSequentialization
