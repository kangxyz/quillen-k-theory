/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassLocalizedSpectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassStableColimit

/-!
# Original perfect inputs to the actual localized Bass telescope

The original inclusion, actual evaluation inverse, original Laurent seed, negative colimit leg,
two coefficient arrows and unchanged perfect K0 law are retained by these consumers.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.SectionBassLocalizedSpectrum

open Quillen

/-- Original bounded-flat inputs use the actual continuous evaluation inverse and initial face. -/
theorem original_bounded_flat_representative (R : CommRingCat.{u}) :
    (boundedFlatPerfectSpectrumIso (Spec R)).hom ≫ affinePerfectBassTelescopeInitialMap R =
      toStableLocalization.map (boundedFlatAffineSectionEvaluationInversePrespectrumMap R ≫
        boundedFlatAffineSectionBassTelescopeInitial.app R) := by
  rw [affinePerfectBassTelescopeInitialMap_eq, Iso.hom_inv_id_assoc]

/-- The first actual telescope cylinder transports the initial map across the unchanged unit seed.
-/
theorem original_seed_first_stage (R : CommRingCat.{u}) :
    affinePerfectBassTelescopeInitialMap R =
      (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫
        toStableLocalization.map (boundedFlatAffineSectionEvaluationInversePrespectrumMap R ≫
          boundedFlatAffineSectionBassSeed.app R ≫
            (boundedFlatAffineSectionBassTelescopeInclusion 1).app R) := by
  rw [affinePerfectBassTelescopeInitialMap_eq]
  apply congrArg (fun a ↦ (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫ a)
  exact toStableLocalization_map_eq_of_homotopy
    (Homotopy.precomp (boundedFlatAffineSectionEvaluationInversePrespectrumMap R)
      (boundedFlatAffineSectionBassTelescopeInclusionHomotopy R 0))

/-- In every negative degree the actual initial map lands in the original stage-zero colimit leg. -/
theorem original_negative_initial_colimit_leg (R : CommRingCat.{u}) (n : ℕ) :
    (localizedStableHomotopyFunctor (-(n : ℤ) - 1)).map
        (affinePerfectBassTelescopeInitialMap R) ≫
        (boundedFlatAffineSectionBassStableColimitIso R (-(n : ℤ) - 1)).inv =
      (localizedStableHomotopyFunctor (-(n : ℤ) - 1)).map
          (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫
        (stableHomotopyFunctor (-(n : ℤ) - 1)).map
          (boundedFlatAffineSectionEvaluationInversePrespectrumMap R) ≫
        colimit.ι (boundedFlatAffineSectionBassStableDiagram R (-(n : ℤ) - 1)) 0 := by
  have h := congrArg
    (fun f ↦ f ≫ (boundedFlatAffineSectionBassStableColimitIso R (-(n : ℤ) - 1)).inv)
    (boundedFlatAffineSectionBassStableColimitIso_ι_hom R (-(n : ℤ) - 1) 0)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  change colimit.ι (boundedFlatAffineSectionBassStableDiagram R (-(n : ℤ) - 1)) 0 =
    (stableHomotopyFunctor (-(n : ℤ) - 1)).map
      (boundedFlatAffineSectionBassTelescopeInitial.app R) ≫
    (boundedFlatAffineSectionBassStableColimitIso R (-(n : ℤ) - 1)).inv at h
  rw [affinePerfectBassTelescopeInitialMap_stable]
  simp only [Category.assoc, ← h]

/-- Two independent geometric coefficient pullbacks commute with the original initial map. -/
theorem original_two_coefficient_initial {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    perfectLocalizedPullback (Spec.map f) ≫ perfectLocalizedPullback (Spec.map g) ≫
        affinePerfectBassTelescopeInitialMap T =
      affinePerfectBassTelescopeInitialMap R ≫
        toStableLocalization.map (boundedFlatAffineSectionBassTelescopeMap f) ≫
        toStableLocalization.map (boundedFlatAffineSectionBassTelescopeMap g) := by
  have h := affinePerfectBassTelescopeInitialMap_naturality (f ≫ g)
  rw [Spec.map_comp, perfectLocalizedPullback_comp, boundedFlatAffineSectionBassTelescopeMap_comp,
    Functor.map_comp] at h
  simpa only [Category.assoc] using h

/-- The induced zero-degree map preserves exactly the original perfect K0 group operation. -/
theorem original_KZero_addition (R : CommRingCat.{u}) (a b : PerfectK (Spec R) 0) :
    (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
        (originalKStableEquiv (perfectWaldhausen (Spec R)) 0 (Additive.ofMul (a * b))) =
      (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectWaldhausen (Spec R)) 0 (Additive.ofMul a)) +
        (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectWaldhausen (Spec R)) 0 (Additive.ofMul b)) := by
  change (localizedStableHomotopyFunctor 0).map (affinePerfectBassTelescopeInitialMap R)
    (originalKStableEquiv (perfectWaldhausen (Spec R)) 0
      (Additive.ofMul a + Additive.ofMul b)) = _
  rw [map_add, map_add]

/-- On flat coefficients the unchanged old exact flat-pullback K-map is retained. -/
theorem original_flat_K_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) [Flat (Spec.map f)]
    (n : ℕ) (a : PerfectK (Spec R) n) :
    (localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap S)
        (originalKStableEquiv (perfectWaldhausen (Spec S)) n
          (Additive.ofMul (perfectKFlatPullback (Spec.map f) n a))) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedFlatAffineSectionBassTelescopeMap f)
        ((localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap R)
          (originalKStableEquiv (perfectWaldhausen (Spec R)) n (Additive.ofMul a))) := by
  rw [← perfectKPullback_eq_flatPullback]
  exact affinePerfectBassTelescopeInitialMap_originalK_naturality f n a

end QuillenTest.SectionBassLocalizedSpectrum
