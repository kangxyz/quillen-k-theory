/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeStrictSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope

/-!
# Original Laurent-square telescope-interchange consumers

Every corner and transition below is the unchanged original section Bass tower. The actual
polynomial chart inclusions, full overlap track and independent cone/telescope times are kept.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
universe u
namespace Quillen.Tests.SectionBassTelescopeSquare
local notation "F" => boundedFlatAffineSectionBassDiagram
local notation "τ" => boundedFlatAffineSectionBassTransition

/-- The actual positive polynomial chart keeps its original telescope height. -/
theorem original_left_chart (R : CommRingCat.{u}) (k i : ℕ) (t : unitInterval)
    (x : ((F i).obj (.of (Polynomial R))).space k) :
    (Telescope.diagramSpanIso F τ (laurentSquare R)).hom.map k
      (HomotopyPushout.left
        (boundedFlatAffineSectionBassTelescopeMap (coefficient R))
        (boundedFlatAffineSectionBassTelescopeMap (coefficient R)) k
        (Telescope.cylinder (fun i => (F i).obj (.of (Polynomial R)))
          (fun i => (τ i).app (.of (Polynomial R))) k i (t, x))) =
      Telescope.cylinder
        (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj (laurentSquare R)))
        (Telescope.diagramSpanTransition F τ (laurentSquare R)) k i
        (t, HomotopyPushout.left ((F i).map (coefficient R)) ((F i).map (coefficient R)) k x) := rfl

/-- The actual inverse polynomial chart keeps its original telescope height as well. -/
theorem original_right_chart (R : CommRingCat.{u}) (k i : ℕ) (t : unitInterval)
    (x : ((F i).obj (.of (Polynomial R))).space k) :
    (Telescope.diagramSpanIso F τ (laurentSquare R)).hom.map k
      (HomotopyPushout.right
        (boundedFlatAffineSectionBassTelescopeMap (coefficient R))
        (boundedFlatAffineSectionBassTelescopeMap (coefficient R)) k
        (Telescope.cylinder (fun i => (F i).obj (.of (Polynomial R)))
          (fun i => (τ i).app (.of (Polynomial R))) k i (t, x))) =
      Telescope.cylinder
        (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj (laurentSquare R)))
        (Telescope.diagramSpanTransition F τ (laurentSquare R)) k i
        (t, HomotopyPushout.right
          ((F i).map (coefficient R)) ((F i).map (coefficient R)) k x) := rfl

/-- The original overlap time and original tower height stay independent. -/
theorem original_overlap_two_times (R : CommRingCat.{u}) (k i : ℕ) (s t : unitInterval)
    (x : ((F i).obj R).space k) :
    (Telescope.diagramSpanIso F τ (laurentSquare R)).hom.map k
      (HomotopyPushout.cylinder
        (boundedFlatAffineSectionBassTelescopeMap (coefficient R))
        (boundedFlatAffineSectionBassTelescopeMap (coefficient R)) k
        (s, Telescope.cylinder (fun i => (F i).obj R) (fun i => (τ i).app R) k i (t, x))) =
      Telescope.cylinder
        (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj (laurentSquare R)))
        (Telescope.diagramSpanTransition F τ (laurentSquare R)) k i
        (t, HomotopyPushout.cylinder ((F i).map (coefficient R)) ((F i).map (coefficient R)) k
          (s, x)) := rfl

/-- The actual final Laurent comparison is preserved as the original whole prespectrum arrow. -/
theorem original_laurent_comparison (R : CommRingCat.{u}) :
    (Telescope.diagramSpanIso F τ (laurentSquare R)).hom ≫
      Telescope.diagramComparisonMap F τ (laurentSquare R) =
        StrictSquare.comparison
          (boundedFlatAffineSectionBassTelescopeFunctor.mapArrow.mapArrow.obj (laurentSquare R)) :=
  Telescope.diagramSpanIso_comparison F τ (laurentSquare R)

/-- The initial Laurent cone target at height one retains the single original Laurent seed. -/
theorem original_laurent_seed_gluing (R : CommRingCat.{u}) (k : ℕ)
    (y : (boundedFlatAffineSectionPrespectrumFunctor.obj (.of (LaurentPolynomial R))).space k) :
    (Telescope.diagramConeIso F τ (laurentSquare R)).inv.map k
      (Telescope.cylinder
        (fun i => mappingCone (StrictSquare.comparison
          ((F i).mapArrow.mapArrow.obj (laurentSquare R))))
        (Telescope.diagramConeTransition F τ (laurentSquare R)) k 0
        (1, (mappingConeInclusion
          (StrictSquare.comparison ((F 0).mapArrow.mapArrow.obj (laurentSquare R)))).map k y)) =
      (mappingConeInclusion (StrictSquare.comparison
        (boundedFlatAffineSectionBassTelescopeFunctor.mapArrow.mapArrow.obj
          (laurentSquare R)))).map k
        (Telescope.cylinder (fun i => (F i).obj (.of (LaurentPolynomial R)))
          (fun i => (τ i).app (.of (LaurentPolynomial R))) k 1
          (0, (boundedFlatAffineSectionBassSeed.app (.of (LaurentPolynomial R))).map k y)) := by
  rw [Telescope.diagramConeIso_inv_target, Telescope.cylinder_one]
  rfl

/-- An actual cone class has unchanged independent cone time and telescope height. -/
theorem original_cone_two_times (R : CommRingCat.{u}) (k i : ℕ) (s t : unitInterval)
    (x : (StrictSquare.span ((F i).mapArrow.mapArrow.obj (laurentSquare R))).space k) :
    (Telescope.diagramConeIso F τ (laurentSquare R)).inv.map k
      (Telescope.cylinder
        (fun i => mappingCone (StrictSquare.comparison
          ((F i).mapArrow.mapArrow.obj (laurentSquare R))))
        (Telescope.diagramConeTransition F τ (laurentSquare R)) k i
        (t, ReducedMappingCone.cylinder
          ((StrictSquare.span ((F i).mapArrow.mapArrow.obj (laurentSquare R))).point k)
          (((F i).obj (.of (LaurentPolynomial R))).point k)
          ((StrictSquare.comparison ((F i).mapArrow.mapArrow.obj
            (laurentSquare R))).map k) (s, x))) =
      ReducedMappingCone.cylinder
        ((StrictSquare.span
          (boundedFlatAffineSectionBassTelescopeFunctor.mapArrow.mapArrow.obj
            (laurentSquare R))).point k)
        ((boundedFlatAffineSectionBassTelescope (.of (LaurentPolynomial R))).point k)
        ((StrictSquare.comparison
          (boundedFlatAffineSectionBassTelescopeFunctor.mapArrow.mapArrow.obj
            (laurentSquare R))).map k)
        (s, (Telescope.diagramSpanIso F τ (laurentSquare R)).inv.map k
          (Telescope.cylinder
            (fun i => StrictSquare.span ((F i).mapArrow.mapArrow.obj (laurentSquare R)))
            (Telescope.diagramSpanTransition F τ (laurentSquare R)) k i (t, x))) :=
  Telescope.diagramConeIso_inv_cylinder F τ (laurentSquare R) k i s t x

end Quillen.Tests.SectionBassTelescopeSquare
