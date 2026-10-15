/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassFunctorStableEquivalence

/-!
# Actual Bass stable-preservation consumers

These consumers use the original Laurent coefficient square and its actual coefficient map,
negative signed groups, the original parameter-loop map with its independent loop time, and
strict natural transformations of the genuine finite-stage diagrams.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassFunctorStableEquivalence

open Quillen

/-- The original Laurent square at an actual finite geometric stage. -/
def originalLaurentSquare (i : ℕ) (R : CommRingCat.{u}) :
    Arrow (Arrow LoopPrespectrum.{u + 1}) :=
  (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R)

/-- The unchanged map induced by the original coefficient arrow. -/
def originalLaurentSquareMap (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    originalLaurentSquare i R ⟶ originalLaurentSquare i S :=
  (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.map f)

/-- Actual coefficient maps after Bass are stable from the four original stable coefficients. -/
theorem actual_bass_coefficient_stable (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (h00 : IsStableEquivalence (originalLaurentSquareMap i f).left.left)
    (h01 : IsStableEquivalence (originalLaurentSquareMap i f).left.right)
    (h10 : IsStableEquivalence (originalLaurentSquareMap i f).right.left)
    (h11 : IsStableEquivalence (originalLaurentSquareMap i f).right.right) :
    IsStableEquivalence
      ((KTheory.Bass.strictRingDiagramFunctor.obj (boundedFlatAffineSectionBassDiagram i)).map f) :=
  boundedFlatAffineSectionBass_squareMap_isStableEquivalence i i _ _
    (originalLaurentSquareMap i f) h00 h01 h10 h11

/-- The unchanged Bass coefficient map is invertible in every original negative stable degree. -/
theorem actual_bass_coefficient_negative_iso (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (h00 : IsStableEquivalence (originalLaurentSquareMap i f).left.left)
    (h01 : IsStableEquivalence (originalLaurentSquareMap i f).left.right)
    (h10 : IsStableEquivalence (originalLaurentSquareMap i f).right.left)
    (h11 : IsStableEquivalence (originalLaurentSquareMap i f).right.right) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      ((KTheory.Bass.strictRingDiagramFunctor.obj
        (boundedFlatAffineSectionBassDiagram i)).map f)) :=
  actual_bass_coefficient_stable i f h00 h01 h10 h11 _

/-- The actual Laurent comparison has no residual excision premise in negative degrees. -/
theorem actual_laurent_comparison_negative_iso (i : ℕ) (R : CommRingCat.{u}) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (mappingConeFiberComparison (StrictSquare.comparison (originalLaurentSquare i R)))) :=
  boundedFlatAffineSectionBass_square_coneFiber_isStableEquivalence i _ _

/-- The unchanged Bass map acts on each original loop value with its independent parameter. -/
theorem actual_bass_loop_value (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (p : Path
      ((mappingCone (StrictSquare.comparison (originalLaurentSquare i R))).point n)
      ((mappingCone (StrictSquare.comparison (originalLaurentSquare i R))).point n))
    (t : unitInterval) :
    Path.toContinuousMap (show Path _ _ from
      (((KTheory.Bass.strictRingDiagramFunctor.obj
        (boundedFlatAffineSectionBassDiagram i)).map f).map n p)) t =
      (mappingConeMap (strictSquareComparisonFunctor.map (originalLaurentSquareMap i f))).map n
        (p t) := rfl

/-- A genuine finite-stage transformation stays invertible on signed groups after actual Bass. -/
theorem actual_transformation_signed_iso (i j : ℕ)
    (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassDiagram j)
    (hη : ∀ R, IsStableEquivalence (η.app R)) (R : CommRingCat.{u}) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map ((KTheory.Bass.strictRingDiagramFunctor.map η).app R)) :=
  boundedFlatAffineSectionBass_functorMap_isStableEquivalence i j η hη R d

/-- The original transformed arrow commutes literally with every coefficient map. -/
theorem actual_transformation_coefficient_square (i j : ℕ)
    (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassDiagram j)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((KTheory.Bass.strictRingDiagramFunctor.obj (boundedFlatAffineSectionBassDiagram i)).map f) ≫
        (KTheory.Bass.strictRingDiagramFunctor.map η).app S =
      (KTheory.Bass.strictRingDiagramFunctor.map η).app R ≫
        ((KTheory.Bass.strictRingDiagramFunctor.obj
          (boundedFlatAffineSectionBassDiagram j)).map f) :=
  (KTheory.Bass.strictRingDiagramFunctor.map η).naturality f

end QuillenTest.SectionBassFunctorStableEquivalence
