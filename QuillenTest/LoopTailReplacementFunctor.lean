/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacementStableNaturality
public import Quillen.Topology.Prespectrum.LoopTailOmega

/-!
# Original-map consumers of the strict Omega replacement functor

The original cylinder height survives strict composition, each iterate retains its loop
coordinate, and the original initial inclusion is natural pointwise. Signed stable-class
compatibility is checked in both directions. A supplied original stable equivalence yields the
actual strict replacement arrow between the proved Omega spectra and reflects equality of
arbitrary signed stable classes. No homotopy-only telescope laws are substituted for strict laws.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace QuillenTest.LoopTailReplacementFunctor

open Quillen

/-- Strict composite replacement maps retain the original whole cylinder and its exact height. -/
theorem original_composite_cylinder {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)
    (k i : ℕ) (s : unitInterval) (x : (loopTailIterate E i).space k) :
    (loopTailReplacementFunctor.map (f ≫ g)).map k
      (Telescope.cylinder (loopTailIterate E) (loopTailTransition E) k i (s, x)) =
      Telescope.cylinder (loopTailIterate G) (loopTailTransition G) k i
        (s, (loopTailIterateMap g i).map k ((loopTailIterateMap f i).map k x)) := by
  change (loopTailReplacementMap (f ≫ g)).map k _ = _
  rw [loopTailReplacementMap_cylinder, loopTailIterateMap_comp]
  rfl

/-- The original initial inclusion commutes pointwise with the actual functor map. -/
theorem original_unit_pointwise {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (k : ℕ) (x : E.space k) :
    (loopTailReplacementFunctor.map f).map k ((loopTailReplacementUnit.app E).map k x) =
      (loopTailReplacementUnit.app F).map k (f.map k x) := rfl

/-- Every iterated loop parameter is unchanged by the original next-level map. -/
theorem original_iterated_loop_parameter {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (i k : ℕ) (γ : Path ((loopTailIterate E i).point (k + 1))
      ((loopTailIterate E i).point (k + 1))) (t : unitInterval) :
    Path.toContinuousMap ((loopTailIterateMap f (i + 1)).map k γ) t =
      (loopTailIterateMap f i).map (k + 1) (γ t) := loopTailIterateMap_succ_apply f i k γ t

variable {E F : LoopPrespectrum.{u}} [∀ k, T1Space (E.space k)] [∀ k, T1Space (F.space k)]

/-- The unchanged initial-inclusion comparison sends every original signed class naturally. -/
theorem original_signed_class_naturality (f : E ⟶ F) (d : ℤ) (a : stableHomotopyGroup E d) :
    (stableHomotopyFunctor d).map (loopTailReplacementFunctor.map f)
      ((loopTailReplacementStableHomotopyIso E d).hom a) =
      (loopTailReplacementStableHomotopyIso F d).hom ((stableHomotopyFunctor d).map f a) :=
  ConcreteCategory.congr_hom (loopTailReplacementStableHomotopyIso_naturality f d) a

/-- Returning an arbitrary replacement class through the inverse original unit comparison is
compatible with the actual original map, in every signed degree. -/
theorem original_inverse_signed_class_naturality (f : E ⟶ F) (d : ℤ)
    (a : stableHomotopyGroup (loopTailReplacement E) d) :
    (loopTailReplacementStableHomotopyIso F d).inv
      ((stableHomotopyFunctor d).map (loopTailReplacementFunctor.map f) a) =
      (stableHomotopyFunctor d).map f ((loopTailReplacementStableHomotopyIso E d).inv a) :=
  (ConcreteCategory.congr_hom (loopTailReplacementStableHomotopyIso_inv_naturality f d) a).symm

/-- An original stable equivalence gives the actual strict arrow between the proved Omega
replacements, with its original stable-equivalence property. -/
theorem original_stable_arrow_between_omega_replacements (f : E ⟶ F)
    (hf : IsStableEquivalence f) :
    (loopTailReplacementFunctor.obj E).IsOmega ∧
      (loopTailReplacementFunctor.obj F).IsOmega ∧
        IsStableEquivalence (loopTailReplacementFunctor.map f) :=
  ⟨loopTailReplacement_isOmega E, loopTailReplacement_isOmega F,
    loopTailReplacementMap_isStableEquivalence f hf⟩

/-- Equality of arbitrary signed replacement classes is reflected by the actual functor map
of an original stable equivalence. -/
theorem original_replacement_stable_class_equality_reflected (f : E ⟶ F)
    (hf : IsStableEquivalence f) (d : ℤ)
    (a b : stableHomotopyGroup (loopTailReplacement E) d)
    (hab : (stableHomotopyFunctor d).map (loopTailReplacementFunctor.map f) a =
      (stableHomotopyFunctor d).map (loopTailReplacementFunctor.map f) b) : a = b := by
  have : IsIso ((stableHomotopyFunctor d).map (loopTailReplacementFunctor.map f)) :=
    loopTailReplacementMap_isStableEquivalence f hf d
  exact (ConcreteCategory.bijective_of_isIso
    ((stableHomotopyFunctor d).map (loopTailReplacementFunctor.map f))).injective hab

end QuillenTest.LoopTailReplacementFunctor
