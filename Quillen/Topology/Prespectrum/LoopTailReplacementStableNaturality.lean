/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacementFunctor

/-!
# Original stable-map naturality of the loop-tail replacement

The original stage inclusions and all-integer stable maps commute with the strict replacement
map. With exactly the existing T1 hypotheses on the original source and target levels, the
previously constructed unit-induced stable isomorphisms are natural for those original maps.
Their actual conjugacy proves preservation and reflection of stable equivalences. No assertion
that the unit is levelwise weak or that the functor preserves homotopy cones is made.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

/-- The strict original loop-tail action preserves stable equivalences without a T1 hypothesis. -/
theorem loopTailFunctor_map_isStableEquivalence {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence f) : IsStableEquivalence (loopTailFunctor.map f) := by
  intro d
  let s := stableHomotopyFunctor d
  have := stabilizationMap_isStableEquivalence E d
  have := stabilizationMap_isStableEquivalence F d
  have := hf d
  have hn := congrArg s.map (stabilizationMap_naturality f)
  simp only [Functor.map_comp] at hn
  have he : s.map (loopTailFunctor.map f) =
      inv (s.map (stabilizationMap E)) ≫ s.map f ≫ s.map (stabilizationMap F) := by
    apply (cancel_epi (s.map (stabilizationMap E))).mp
    rw [IsIso.hom_inv_id_assoc]
    exact hn.symm
  rw [he]
  infer_instance

/-- Every actual tower map preserves an original stable equivalence. -/
theorem loopTailIterateMap_isStableEquivalence {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence f) (i : ℕ) : IsStableEquivalence (loopTailIterateMap f i) := by
  induction i with
  | zero => exact hf
  | succ i ih => exact loopTailFunctor_map_isStableEquivalence (loopTailIterateMap f i) ih

/-- The actual replacement map retains every original stage inclusion on every signed class. -/
theorem loopTailReplacementMap_stable_inclusion_apply {E F : LoopPrespectrum.{u}}
    (f : E ⟶ F) (d : ℤ) (i : ℕ) (a : stableHomotopyGroup (loopTailIterate E i) d) :
    (stableHomotopyFunctor d).map (loopTailReplacementMap f)
      ((stableHomotopyFunctor d).map
        (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) i) a) =
      (stableHomotopyFunctor d).map
        (Telescope.inclusion (loopTailIterate F) (loopTailTransition F) i)
        ((stableHomotopyFunctor d).map (loopTailIterateMap f i) a) := by
  have h := congrArg ((stableHomotopyFunctor d).map) (loopTailReplacementMap_inclusion f i)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h a

variable {E F : LoopPrespectrum.{u}} [∀ k, T1Space (E.space k)] [∀ k, T1Space (F.space k)]

/-- The original unit-induced stable isomorphisms are natural for the unchanged strict map. -/
@[reassoc] theorem loopTailReplacementStableHomotopyIso_naturality (f : E ⟶ F) (d : ℤ) :
    (loopTailReplacementStableHomotopyIso E d).hom ≫
        (stableHomotopyFunctor d).map (loopTailReplacementMap f) =
      (stableHomotopyFunctor d).map f ≫ (loopTailReplacementStableHomotopyIso F d).hom := by
  rw [loopTailReplacementStableHomotopyIso_hom, loopTailReplacementStableHomotopyIso_hom,
    ← Functor.map_comp, ← Functor.map_comp, loopTailReplacementInclusion_naturality]

/-- The actual replacement-induced stable map is the conjugate of the original map by the
existing initial-inclusion comparisons, in every integer degree. -/
theorem loopTailReplacementMap_stableMap_eq (f : E ⟶ F) (d : ℤ) :
    (stableHomotopyFunctor d).map (loopTailReplacementMap f) =
      (loopTailReplacementStableHomotopyIso E d).inv ≫
        (stableHomotopyFunctor d).map f ≫ (loopTailReplacementStableHomotopyIso F d).hom := by
  apply (cancel_epi (loopTailReplacementStableHomotopyIso E d).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact loopTailReplacementStableHomotopyIso_naturality f d

/-- The inverse comparisons also commute with the unchanged original stable maps. -/
@[reassoc] theorem loopTailReplacementStableHomotopyIso_inv_naturality (f : E ⟶ F) (d : ℤ) :
    (loopTailReplacementStableHomotopyIso E d).inv ≫ (stableHomotopyFunctor d).map f =
      (stableHomotopyFunctor d).map (loopTailReplacementMap f) ≫
        (loopTailReplacementStableHomotopyIso F d).inv := by
  rw [loopTailReplacementMap_stableMap_eq]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The same original map is stable exactly when its actual replacement map is stable. -/
theorem loopTailReplacementMap_isStableEquivalence_iff (f : E ⟶ F) :
    IsStableEquivalence (loopTailReplacementMap f) ↔ IsStableEquivalence f := by
  constructor
  · intro hf d
    have := hf d
    have he : (stableHomotopyFunctor d).map f =
        (loopTailReplacementStableHomotopyIso E d).hom ≫
          (stableHomotopyFunctor d).map (loopTailReplacementMap f) ≫
            (loopTailReplacementStableHomotopyIso F d).inv := by
      rw [loopTailReplacementStableHomotopyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  · intro hf d
    have := hf d
    rw [loopTailReplacementMap_stableMap_eq]
    infer_instance

/-- The strict original replacement functor preserves stable equivalences under the original
source and target T1 hypotheses. -/
theorem loopTailReplacementMap_isStableEquivalence (f : E ⟶ F) (hf : IsStableEquivalence f) :
    IsStableEquivalence (loopTailReplacementMap f) :=
  (loopTailReplacementMap_isStableEquivalence_iff f).mpr hf

end Quillen.LoopPrespectrum
