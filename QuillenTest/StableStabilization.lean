/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacement
public import Quillen.Topology.Prespectrum.FiberDetection

/-!
# Original-map consumers of loop-tail stabilization

The actual structure map and its two independent loop parameters are retained. The inverse stable
comparison is evaluated on an original stage representative, and the actual stabilization fiber
has vanishing signed groups. Under T1 separation, the actual telescope inclusion detects equality
of original stable classes, with its literal zeroth-stage point unchanged.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace QuillenTest.StableStabilization

open Quillen

/-- The stabilization target uses the original untransposed ordering of its two loop parameters. -/
theorem original_loop_tail_structure_parameters (E : LoopPrespectrum.{u}) (n : ℕ)
    (γ : Path (E.point (n + 1)) (E.point (n + 1))) (s t : unitInterval) :
    Path.toContinuousMap ((looping (tail E)).structureMap n γ s) t =
      E.structureMap (n + 1) (γ s) t := rfl

/-- Applying the inverse to an actual target-stage class returns precisely the next original
source-stage class through its genuine loop-degree shift, in every integer degree. -/
theorem original_stage_class_return (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ)
    (a : (stableSystem (looping (tail E)) d).obj n) :
    (stabilizationStableHomotopyIso E d).inv (stableHomotopyι (looping (tail E)) d n a) =
      stableHomotopyι E d (n + 1) (stabilizationStageReturn E d n a) :=
  ConcreteCategory.congr_hom (stabilizationStableHomotopyIso_ι_inv E d n) a

/-- The existing actual all-integer fiber LES detects vanishing for the original stabilization
map, with no assumptions on the original spaces or their connectivity. -/
theorem original_stabilization_fiber_vanishes (E : LoopPrespectrum.{u}) (d : ℤ) :
    Subsingleton (stableHomotopyGroup (homotopyFiber (stabilizationMap E)) d) :=
  stableFiber_subsingleton_of_isStableEquivalence (stabilizationMap E)
    (stabilizationMap_isStableEquivalence E) d

/-- The replacement map is the literal zero-time inclusion of the unchanged original point. -/
theorem original_replacement_point (E : LoopPrespectrum.{u}) (n : ℕ) (x : E.space n) :
    (loopTailReplacementInclusion E).map n x =
      Telescope.cylinder (loopTailIterate E) (loopTailTransition E) n 0 (0, x) := rfl

/-- The actual initial-stage telescope inclusion detects equality of original stable classes,
including negative degrees, under the explicit original T1 hypothesis. -/
theorem original_replacement_detects_stable_class (E : LoopPrespectrum.{u})
    [∀ k, T1Space (E.space k)] (d : ℤ) (a b : stableHomotopyGroup E d) :
    (stableHomotopyFunctor d).map (loopTailReplacementInclusion E) a =
      (stableHomotopyFunctor d).map (loopTailReplacementInclusion E) b ↔ a = b := by
  exact ((ConcreteCategory.isIso_iff_bijective _).mp
    (loopTailReplacementInclusion_isStableEquivalence E d)).injective.eq_iff

end QuillenTest.StableStabilization
