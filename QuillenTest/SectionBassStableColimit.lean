/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassStableColimit

/-!
# Original stage, seed and coefficient consumers of the actual Bass stable colimit

These tests retain the original seed, degree-zero chosen point, all negative stable degrees,
stage representatives and two independent coefficient changes without extra topology premises.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionBassStableColimit

open Quillen

/-- The first actual stable connecting arrow is the stable map of the unchanged Laurent seed. -/
theorem original_seed_stable_arrow (R : CommRingCat.{u}) (d : ℤ) :
    (boundedFlatAffineSectionBassStableDiagram R d).map (homOfLE (Nat.zero_le 1)) =
      (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassSeed.app R) := rfl

/-- Even one more literal loop of an arbitrary stage has a well-based zero-level point. -/
theorem original_iterated_extra_loop_point (R : CommRingCat.{u}) (i : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((parameterLooping ((boundedFlatAffineSectionBassDiagram i).obj R)).point 0))) :=
  parameterLooping_point_homotopyExtensionProperty _ 0 isClosed_singleton
    (boundedFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R 0)

/-- The comparison sends the original zero-stage leg to the unchanged initial inclusion. -/
theorem original_initial_stable_leg (R : CommRingCat.{u}) (d : ℤ) :
    colimit.ι (boundedFlatAffineSectionBassStableDiagram R d) 0 ≫
        (boundedFlatAffineSectionBassStableColimitIso R d).hom =
      (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeInitial.app R) :=
  boundedFlatAffineSectionBassStableColimitIso_ι_hom R d 0

/-- Every actual negative stable class has a representative in an unchanged original stage. -/
theorem original_negative_stage_representative (R : CommRingCat.{u}) (n : ℕ)
    (a : stableHomotopyGroup (boundedFlatAffineSectionBassTelescope R) (-(n : ℤ) - 1)) :
    ∃ i : ℕ, ∃ b : stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram i).obj R)
      (-(n : ℤ) - 1),
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map
        ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) b = a :=
  Telescope.exists_stable_representative
    (fun i ↦ (boundedFlatAffineSectionBassDiagram i).obj R)
    (fun i ↦ (boundedFlatAffineSectionBassTransition i).app R) (-(n : ℤ) - 1) a

/-- The actual negative comparison inverse recovers the literal original stage-colimit leg. -/
theorem original_negative_inverse (R : CommRingCat.{u}) (n i : ℕ)
    (a : stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram i).obj R) (-(n : ℤ) - 1)) :
    (boundedFlatAffineSectionBassStableColimitIso R (-(n : ℤ) - 1)).inv
        ((stableHomotopyFunctor (-(n : ℤ) - 1)).map
          ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) a) =
      colimit.ι (boundedFlatAffineSectionBassStableDiagram R (-(n : ℤ) - 1)) i a := by
  apply (ConcreteCategory.bijective_of_isIso
    (boundedFlatAffineSectionBassStableColimitIso R (-(n : ℤ) - 1)).hom).1
  exact (ConcreteCategory.congr_hom
    (boundedFlatAffineSectionBassStableColimitIso R (-(n : ℤ) - 1)).inv_hom_id _).trans
      (ConcreteCategory.congr_hom
        (boundedFlatAffineSectionBassStableColimitIso_ι_hom R (-(n : ℤ) - 1) i) a).symm

/-- Two original coefficient changes agree through the actual signed natural comparison. -/
theorem original_two_coefficient_square {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (d : ℤ) :
    (boundedFlatAffineSectionBassStableColimitFunctor d).map f ≫
        (boundedFlatAffineSectionBassStableColimitFunctor d).map g ≫
        (boundedFlatAffineSectionBassStableColimitIso T d).hom =
      (boundedFlatAffineSectionBassStableColimitIso R d).hom ≫
        (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap f) ≫
        (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeMap g) := by
  change colimMap (boundedFlatAffineSectionBassStableDiagramMap f d) ≫
      colimMap (boundedFlatAffineSectionBassStableDiagramMap g d) ≫
      (boundedFlatAffineSectionBassStableColimitIso T d).hom = _
  rw [boundedFlatAffineSectionBassStableColimitIso_naturality,
    boundedFlatAffineSectionBassStableColimitIso_naturality_assoc, Category.assoc]


end QuillenTest.SectionBassStableColimit
