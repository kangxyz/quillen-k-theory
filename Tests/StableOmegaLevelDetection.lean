/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.StableOmegaLevelDetection
public import Quillen.Topology.Prespectrum.LoopTailReplacementStableNaturality
public import Quillen.Topology.Prespectrum.LoopTailOmega

/-!
# Original-map consumers of all-component Omega detection

The consumers retain arbitrary original source points, target points, finite degrees, signed
stable degrees, actual replacement maps, and the unchanged initial inclusion. No connectedness
or positive-level-only restriction is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory Quillen Quillen.LoopPrespectrum

universe u

namespace Quillen.Tests.StableOmegaLevelDetection

/-- Every actual target point lies in the image component of the unchanged level map. -/
theorem original_target_component_lift {E F : LoopPrespectrum.{u}}
    (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F) (hf : IsStableEquivalence f)
    (k : ℕ) (y : F.space k) : ∃ x : E.space k, Nonempty (Path (f.map k x) y) :=
  (level_isWeakHomotopyEquivalence_of_isStableEquivalence hE hF f hf k).component_surjective y

/-- A target class at the image of any actual source point lifts under the original map. -/
theorem original_arbitrary_point_class_lift {E F : LoopPrespectrum.{u}}
    (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F) (hf : IsStableEquivalence f)
    (k n : ℕ) (x : E.space k) (b : HomotopyGroup.Pi n (F.space k) (f.map k x)) :
    ∃ a : HomotopyGroup.Pi n (E.space k) x, homotopyGroupMap (f.map k) rfl a = b :=
  ((level_isWeakHomotopyEquivalence_of_isStableEquivalence hE hF f hf k).homotopy_bijective
    x n).surjective b

/-- Equality of classes based at an arbitrary original point is reflected, including degree zero. -/
theorem original_arbitrary_point_class_reflection {E F : LoopPrespectrum.{u}}
    (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F) (hf : IsStableEquivalence f)
    (k n : ℕ) (x : E.space k) (a b : HomotopyGroup.Pi n (E.space k) x)
    (hab : homotopyGroupMap (f.map k) rfl a = homotopyGroupMap (f.map k) rfl b) : a = b :=
  ((level_isWeakHomotopyEquivalence_of_isStableEquivalence hE hF f hf k).homotopy_bijective
    x n).injective hab

/-- Each unchanged signed stable stage already lifts target classes for a stable Omega map. -/
theorem original_signed_stage_lift {E F : LoopPrespectrum.{u}}
    (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F) (hf : IsStableEquivalence f)
    (d : ℤ) (i : ℕ) (b : (stableSystem F d).obj i) :
    ∃ a : (stableSystem E d).obj i, (stableSystemMap f d).app i a = b :=
  (stableSystemMap_app_bijective_of_isStableEquivalence hE hF f hf d i).surjective b

/-- The same original replacement arrow detects stable equivalence by complete weakness at
all levels, under only the existing source and target levelwise T1 hypotheses. -/
theorem original_replacement_map_detection {E F : LoopPrespectrum.{u}}
    [∀ k, T1Space (E.space k)] [∀ k, T1Space (F.space k)] (f : E ⟶ F) :
    IsStableEquivalence f ↔ ∀ k, IsWeakHomotopyEquivalence ((loopTailReplacementMap f).map k) :=
  (loopTailReplacementMap_isStableEquivalence_iff f).symm.trans
    (isStableEquivalence_iff_levelwise_of_isOmega (loopTailReplacement_isOmega E)
      (loopTailReplacement_isOmega F) (loopTailReplacementMap f))

/-- For an already genuine Omega-prespectrum, the unchanged initial inclusion is completely
weak at every level, without imposing T1 on the telescope levels. -/
theorem original_omega_initial_inclusion_isWeakHomotopyEquivalence
    (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)] (hE : E.IsOmega) (k : ℕ) :
    IsWeakHomotopyEquivalence ((loopTailReplacementInclusion E).map k) :=
  level_isWeakHomotopyEquivalence_of_isStableEquivalence hE (loopTailReplacement_isOmega E)
    (loopTailReplacementInclusion E) (loopTailReplacementInclusion_isStableEquivalence E) k

end Quillen.Tests.StableOmegaLevelDetection
