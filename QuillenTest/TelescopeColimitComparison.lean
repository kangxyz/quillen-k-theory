/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeHomotopyColimit
import Quillen.Topology.Prespectrum.TelescopeStableColimit

/-!
# Original-map consumers of the canonical telescope colimit comparisons

The comparisons and their inverses recover the literal original stage maps,
including degree-zero components and negative stable degrees. The stable
comparison preserves sums represented at different stages and retains the
original strict-diagram naturality square.
-/

open CategoryTheory CategoryTheory.Limits
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeColimitComparison

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The component-set comparison inverse returns the original stage-colimit representative. -/
theorem original_component_inverse (k : ℕ) [∀ i, T1Space ((E i).space k)] (i : ℕ)
    (a : HomotopyGroup.Pi 0 ((E i).space k) ((E i).point k)) :
    (Telescope.homotopyColimitIso E f k 0).inv
        (homotopyGroupMap ((Telescope.inclusion E f i).map k)
          ((Telescope.inclusion E f i).map_point k) a) =
      colimit.ι (Telescope.homotopyDiagram E f k 0) i a := by
  apply (ConcreteCategory.bijective_of_isIso (Telescope.homotopyColimitIso E f k 0).hom).1
  exact (ConcreteCategory.congr_hom (Telescope.homotopyColimitIso E f k 0).inv_hom_id _).trans
    (ConcreteCategory.congr_hom (Telescope.homotopyColimitIso_ι_hom E f k 0 i) a).symm

variable [∀ i k, T1Space ((E i).space k)]

/-- The negative stable comparison inverse recovers the original stage-colimit representative. -/
theorem original_negative_inverse (n i : ℕ)
    (a : stableHomotopyGroup (E i) (-(n : ℤ) - 1)) :
    (Telescope.stableColimitIso E f (-(n : ℤ) - 1)).inv
        ((stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.inclusion E f i) a) =
      colimit.ι (Telescope.stageStableDiagram E f (-(n : ℤ) - 1)) i a := by
  apply (ConcreteCategory.bijective_of_isIso
    (Telescope.stableColimitIso E f (-(n : ℤ) - 1)).hom).1
  exact (ConcreteCategory.congr_hom
    (Telescope.stableColimitIso E f (-(n : ℤ) - 1)).inv_hom_id _).trans
      (ConcreteCategory.congr_hom (Telescope.stableColimitIso_ι_hom E f (-(n : ℤ) - 1) i) a).symm

/-- Addition of classes from different stages agrees with the original telescope group law. -/
theorem original_sum_from_two_stages (d : ℤ) (i j : ℕ)
    (a : stableHomotopyGroup (E i) d) (b : stableHomotopyGroup (E j) d) :
    (Telescope.stableColimitIso E f d).hom
        (colimit.ι (Telescope.stageStableDiagram E f d) i a +
          colimit.ι (Telescope.stageStableDiagram E f d) j b) =
      (stableHomotopyFunctor d).map (Telescope.inclusion E f i) a +
        (stableHomotopyFunctor d).map (Telescope.inclusion E f j) b := by
  exact ((Telescope.stableColimitIso E f d).hom.hom.map_add _ _).trans
    (congrArg₂ (· + ·)
      (ConcreteCategory.congr_hom (Telescope.stableColimitIso_ι_hom E f d i) a)
      (ConcreteCategory.congr_hom (Telescope.stableColimitIso_ι_hom E f d j) b))

/-- Negative-degree naturality uses the actual strict-diagram telescope map on the right. -/
theorem original_negative_naturality
    (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
    [∀ i k, T1Space ((E' i).space k)]
    (a : ∀ i, E i ⟶ E' i) (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1)) (n : ℕ)
    (x : ↑(colimit (Telescope.stageStableDiagram E f (-(n : ℤ) - 1)))) :
    (Telescope.stableColimitIso E' f' (-(n : ℤ) - 1)).hom
        (colimMap (Telescope.stageStableDiagramMap E f E' f' a ha (-(n : ℤ) - 1)) x) =
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.map E f E' f' a ha)
        ((Telescope.stableColimitIso E f (-(n : ℤ) - 1)).hom x) :=
  ConcreteCategory.congr_hom
    (Telescope.stableColimitIso_naturality E f E' f' a ha (-(n : ℤ) - 1)) x

end QuillenTest.TelescopeColimitComparison
