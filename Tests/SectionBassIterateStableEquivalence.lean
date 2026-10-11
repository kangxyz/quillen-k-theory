/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassIterateStableEquivalence

/-!
# Original finite Bass iteration consumers

The unchanged iterate map is invertible on every signed stable group whenever the given original
transformation is objectwise stable. Exact stage transports preserve original coefficient maps.
An additional consumer checks iteration of the actual original Laurent seed, without any claim
that this seed is stable and without choosing a new unit or transition.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.SectionBassIterateStableEquivalence

/-- Every negative signed degree uses the same original iterated natural arrow. -/
theorem actual_iterated_negative_iso (n i j : ℕ)
    (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassDiagram j)
    (hη : ∀ R, IsStableEquivalence (η.app R)) (R : CommRingCat.{u}) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (((KTheory.Bass.strictRingDiagramIterate n).map η).app R)) :=
  boundedFlatAffineSectionBass_iterateMap_isStableEquivalence n i j η hη R _

/-- Original coefficient arrows commute with the same actual transformed arrow at every iterate. -/
theorem actual_iterated_coefficient_square (n i j : ℕ)
    (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassDiagram j)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (((KTheory.Bass.strictRingDiagramIterate n).obj
        (boundedFlatAffineSectionBassDiagram i)).map f) ≫
        ((KTheory.Bass.strictRingDiagramIterate n).map η).app S =
      ((KTheory.Bass.strictRingDiagramIterate n).map η).app R ≫
        (((KTheory.Bass.strictRingDiagramIterate n).obj
          (boundedFlatAffineSectionBassDiagram j)).map f) :=
  ((KTheory.Bass.strictRingDiagramIterate n).map η).naturality f

/-- The proved sum-stage transport preserves the literal original coefficient map. -/
theorem actual_iterated_coefficient_transport (n i : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (((KTheory.Bass.strictRingDiagramIterate n).obj
        (boundedFlatAffineSectionBassDiagram i)).map f) ≫
        (eqToHom (boundedFlatAffineSectionBassDiagram_iterate_obj n i)).app S =
      (eqToHom (boundedFlatAffineSectionBassDiagram_iterate_obj n i)).app R ≫
        (boundedFlatAffineSectionBassDiagram (i + n)).map f :=
  (eqToHom (boundedFlatAffineSectionBassDiagram_iterate_obj n i)).naturality f

/-- The original arrow is retained literally at iterate zero. -/
theorem actual_iterated_zero (i j : ℕ)
    (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassDiagram j)
    (R : CommRingCat.{u}) :
    ((KTheory.Bass.strictRingDiagramIterate 0).map η).app R = η.app R := rfl

/-- Addition transport identifies repeated iteration of the SAME proved original Laurent seed. -/
theorem actual_original_seed_iteration (i n : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassTransition (i + n)).app R ≫
        ((eqToHom (KTheory.Bass.strictDiagramIterate_add
          PolynomialBaseChange.laurentSquareFunctor i n)).app
            (KTheory.Bass.strictRingDiagramFunctor.obj
              boundedFlatAffineSectionPrespectrumFunctor)).app R =
      ((eqToHom (KTheory.Bass.strictDiagramIterate_add
        PolynomialBaseChange.laurentSquareFunctor i n)).app
          boundedFlatAffineSectionPrespectrumFunctor).app R ≫
        ((KTheory.Bass.strictRingDiagramIterate n).map
          (boundedFlatAffineSectionBassTransition i)).app R :=
  congrArg (fun a ↦ a.app R)
    ((eqToHom (KTheory.Bass.strictDiagramIterate_add
      PolynomialBaseChange.laurentSquareFunctor i n)).naturality boundedFlatAffineSectionBassSeed)

end Quillen.Tests.SectionBassIterateStableEquivalence
