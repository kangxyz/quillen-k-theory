/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeCone

/-!
# Original double-cylinder and Bass cone-colimit consumers

Both independent times, the actual target inclusion, unchanged Bass coefficients, every signed
stable degree and original finite-stage representative maps remain visible.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.TelescopeConeInterchange
open Telescope PerfectComplexes
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))

/-- The actual isomorphism sends cone time and telescope height to those exact two coordinates.
-/
theorem original_double_cylinder_coordinates (k i : ℕ) (s t : unitInterval)
    (x : (E i).space k) :
    ((coneIso E f F g a ha).hom).map k
      (ReducedMappingCone.cylinder ((prespectrum E f).point k) ((prespectrum F g).point k)
        ((map E f F g a ha).map k) (s, cylinder E f k i (t, x))) =
      cylinder (fun i ↦ mappingCone (a i)) (coneTransition E f F g a ha) k i
        (t, ReducedMappingCone.cylinder ((E i).point k) ((F i).point k) ((a i).map k) (s, x)) :=
  rfl

/-- The actual cone inclusion is carried to the unchanged telescope of stage cone inclusions. -/
theorem original_target_inclusion :
    mappingConeInclusion (map E f F g a ha) ≫ (coneIso E f F g a ha).hom =
      coneInclusion E f F g a ha := coneToTelescope_inclusion E f F g a ha

/-- Every original cone point is recovered by the two explicit descents. -/
theorem original_cone_round_trip (k : ℕ) (q : (mappingCone (map E f F g a ha)).space k) :
    ((coneIso E f F g a ha).inv).map k (((coneIso E f F g a ha).hom).map k q) = q :=
  congrArg (fun h ↦ h.map k q) (coneIso E f F g a ha).hom_inv_id

/-- The genuine section telescope coefficient map retains the strict original cone interchange.
-/
theorem original_bass_cone_inverse {R S : CommRingCat.{u}} (f : R ⟶ S)
    (k : ℕ) (q : (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)).space k) :
    ((boundedFlatAffineSectionBassTelescopeConeIso f).inv).map k
      (((boundedFlatAffineSectionBassTelescopeConeIso f).hom).map k q) = q :=
  congrArg (fun h ↦ h.map k q) (boundedFlatAffineSectionBassTelescopeConeIso f).hom_inv_id

/-- The original negative-degree stage class is carried by its actual stage-cone map. -/
theorem original_bass_negative_stage_class {R S : CommRingCat.{u}} (f : R ⟶ S)
    (i q : ℕ) (z : stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSectionBassDiagram i).map f)) (-(q : ℤ) - 1)) :
    (boundedFlatAffineSectionBassTelescopeConeStableColimitIso f (-(q : ℤ) - 1)).hom
      (colimit.ι (stageStableDiagram
        (fun i ↦ mappingCone ((boundedFlatAffineSectionBassDiagram i).map f))
        (boundedFlatAffineSectionBassConeTransition f) (-(q : ℤ) - 1)) i z) =
      (stableHomotopyFunctor (-(q : ℤ) - 1)).map
        (boundedFlatAffineSectionBassConeStageMap f i) z :=
  ConcreteCategory.congr_hom
    (boundedFlatAffineSectionBassTelescopeConeStableColimitIso_ι_hom f (-(q : ℤ) - 1) i) z

/-- Every unchanged telescope-cone class lifts to an actual finite-stage coefficient cone. -/
theorem original_bass_signed_representative {R S : CommRingCat.{u}} (f : R ⟶ S) (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (boundedFlatAffineSectionBassTelescopeMap f)) d) :
    ∃ i : ℕ, ∃ z : stableHomotopyGroup
      (mappingCone ((boundedFlatAffineSectionBassDiagram i).map f)) d,
      (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassConeStageMap f i) z = x :=
  boundedFlatAffineSectionBassTelescopeCone_exists_stable_representative f d x

end Quillen.Tests.TelescopeConeInterchange
