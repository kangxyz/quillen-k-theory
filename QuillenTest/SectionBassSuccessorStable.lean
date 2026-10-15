/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.Square
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSuccessorStable

/-!
# Original successor, coefficient and signed-stage consumers

The actual loop parameter, negative-degree tail, original Laurent inclusion and two-arrow
coefficient action remain visible through the genuine natural successor isomorphism.
-/
@[expose] public section

open Quillen.PerfectComplexes


open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionBassSuccessorStable

open Quillen

/-- At original level zero, the comparison still retains every loop coordinate. -/
theorem original_zero_level_coefficient (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).space 0) (t : unitInterval) :
    Path.toContinuousMap
      (((boundedFlatAffineSectionBassSuccessorIso i).hom.app S).map 0
        (((boundedFlatAffineSectionBassDiagram (i + 1)).map f).map 0 x)) t =
      (mappingConeMap (strictSquareComparisonFunctor.map
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
          (laurentSquareMap f)))).map 0
        (Path.toContinuousMap (((boundedFlatAffineSectionBassSuccessorIso i).hom.app R).map 0 x)
          t) :=
  boundedFlatAffineSectionBassSuccessorIso_naturality_apply i f 0 x t

/-- The first odd signed-system stage retains the actual negative-degree tail index two. -/
theorem original_negative_odd_stage (i : ℕ) (R : CommRingCat.{u}) :
    stableHomotopyι ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R)
        (-1) 1 ≫
        (boundedFlatAffineSectionBassStableSuccessorIso i (-1)).hom.app R =
      (stableSystemMap ((boundedFlatAffineSectionBassSuccessorIso i).hom.app R)
        (-1)).app 1 ≫
        (alternatingIso 1 (parameterStableStageIso
          ((boundedFlatAffineSectionBassConeDiagram i).obj R) (-1) 1)).hom ≫
        (shiftedStableReindexIso ((boundedFlatAffineSectionBassConeDiagram i).obj R)
          (-1) 1).hom ≫
        stableHomotopyι ((boundedFlatAffineSectionBassConeDiagram i).obj R)
          (-1 + 1) 2 :=
  boundedFlatAffineSectionBassStableSuccessorIso_ι_hom i (-1) R 1

/-- Two successive original coefficient maps agree after the bottom-degree comparison. -/
theorem original_bottom_coefficient_composition (i : ℕ) {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatAffineSectionBassDiagram (i + 1)).map f) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatAffineSectionBassDiagram (i + 1)).map g) ≫
      (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.app T =
    (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.app R ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeMap (strictSquareComparisonFunctor.map
          ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
            (laurentSquareMap (f ≫ g))))) := by
  simpa only [Functor.map_comp, Category.assoc] using
    boundedFlatAffineSectionBassBottomSuccessorIso_naturality i (f ≫ g)

/-- Transport back to the unchanged successor preserves the literal original Laurent class. -/
theorem original_laurent_inclusion_roundtrip (i : ℕ) (R : CommRingCat.{u})
    (x : stableHomotopyGroup
      ((boundedFlatAffineSectionBassDiagram i).obj (.of (LaurentPolynomial R))) (-(i : ℤ))) :
    (boundedFlatAffineSectionBassBottomSuccessorIso i).hom.app R
      ((boundedFlatAffineSectionBassBottomSuccessorIso i).inv.app R
        ((stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
          ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R))))
          x)) =
      (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
        ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R)))) x :=
  ConcreteCategory.congr_hom ((boundedFlatAffineSectionBassBottomSuccessorIso i).app R).inv_hom_id
    ((stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
      ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj (laurentSquare R)))) x)

/-- The inverse bottom comparison also retains the actual original coefficient cone map. -/
theorem original_inverse_bottom_coefficient (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : stableHomotopyGroup ((boundedFlatAffineSectionBassConeDiagram i).obj R) (-(i : ℤ))) :
    (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
      ((boundedFlatAffineSectionBassDiagram (i + 1)).map f)
      ((boundedFlatAffineSectionBassBottomSuccessorIso i).inv.app R x) =
    (boundedFlatAffineSectionBassBottomSuccessorIso i).inv.app S
      ((stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeMap (strictSquareComparisonFunctor.map
          ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
            (laurentSquareMap f)))) x) :=
  (ConcreteCategory.congr_hom
    ((boundedFlatAffineSectionBassBottomSuccessorIso i).inv.naturality f) x).symm

end QuillenTest.SectionBassSuccessorStable
