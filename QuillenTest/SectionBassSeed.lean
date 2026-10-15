/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTransition

/-! Original zero-level Laurent loops, independent structure parameters, and actual iterated seeds.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent
open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SectionBassSeed

open Quillen

/-- At degree zero, the Laurent homotopy applies the original realized action inside the loop. -/
theorem original_zero_level_laurent_loop (R : CommRingCat.{u}) (s t : unitInterval)
    (γ : Path (stagePoint 0 (boundedFlatAffineSectionModel R))
      (stagePoint 0 (boundedFlatAffineSectionModel R))) :
    Path.toContinuousMap ((boundedFlatAffineSectionLaurentUnitHomotopy R).level 0 (s, γ)) t =
      stageTransformationTopHomotopy 0
        (F := boundedFlatAffineSectionModelMap (laurentCoefficient R))
        (G := boundedFlatAffineSectionModelMap (laurentCoefficient R))
        (boundedFlatAffineSectionLaurentPullbackUnitIso R).hom
        (fun A ↦ (boundedFlatAffineSectionModel (.of (LaurentPolynomial R))).waldhausen.weq_iso _
          (by
            change IsIso ((boundedFlatAffineSectionLaurentPullbackUnitIso R).app A).hom
            infer_instance)) (s, γ t) := rfl

/-- The original Laurent homotopy keeps homotopy time separate from structure time. -/
theorem original_laurent_independent_parameters (R : CommRingCat.{u}) (n : ℕ)
    (s t : unitInterval) (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentUnitHomotopy R).level (n + 1)
        (s, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (boundedFlatAffineSectionPrespectrumFunctor.obj (.of (LaurentPolynomial R))).structureMap n
        ((boundedFlatAffineSectionLaurentUnitHomotopy R).level n (s, x)) t :=
  (boundedFlatAffineSectionLaurentUnitHomotopy R).comm n s x t

/-- The actual natural seed, not just its auxiliary map, retains the original concatenated loop.
-/
theorem original_seed_loop (R : CommRingCat.{u}) (n : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassSeed.app R).map n x) t =
      (((boundedFlatAffineSectionLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (StrictSquare.comparison (boundedFlatAffineSectionBassSquare R))))
        |>.conjugateToZero (boundedFlatAffineSectionBassNullHomotopy R)).level n (t, x) := by
  rw [boundedFlatAffineSectionBassSeed_app]
  exact boundedFlatAffineSectionBassSeedMap_apply R n x t

/-- The parameter-loop target retains independent structure and original Laurent loop times. -/
theorem original_seed_independent_parameters (R : CommRingCat.{u}) (n : ℕ)
    (s t : unitInterval) (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    Path.toContinuousMap ((boundedFlatAffineSectionBassSeed.app R).map (n + 1)
        ((boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x s)) t =
      Path.toContinuousMap
        ((parameterLooping (boundedFlatAffineSectionBassCone R)).structureMap n
          ((boundedFlatAffineSectionBassSeed.app R).map n x) s) t := by
  rw [boundedFlatAffineSectionBassSeed_app]
  have h := congrArg (fun p ↦ p s) ((boundedFlatAffineSectionBassSeedMap R).comm n x)
  exact congrArg (fun γ : Path ((boundedFlatAffineSectionBassCone R).point (n + 1))
    ((boundedFlatAffineSectionBassCone R).point (n + 1)) ↦ γ t) h

/-- The same original transition commutes with two independent further coefficient maps. -/
theorem iterated_two_coefficient_square (n : ℕ) {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionBassDiagram n).map f ≫
        (boundedFlatAffineSectionBassDiagram n).map g ≫
        (boundedFlatAffineSectionBassTransition n).app T =
      (boundedFlatAffineSectionBassTransition n).app R ≫
        (boundedFlatAffineSectionBassDiagram (n + 1)).map f ≫
        (boundedFlatAffineSectionBassDiagram (n + 1)).map g := by
  simpa only [Functor.map_comp, Category.assoc] using
    boundedFlatAffineSectionBassTransition_naturality n (f ≫ g)

/-- Every iterated image is a based map on the actual stage, in every prespectrum level. -/
theorem iterated_original_point (i n : ℕ) (R : CommRingCat.{u}) :
    ((boundedFlatAffineSectionBassTransition i).app R).map n
        (((boundedFlatAffineSectionBassDiagram i).obj R).point n) =
      ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).point n :=
  ((boundedFlatAffineSectionBassTransition i).app R).map_point n

end QuillenTest.SectionBassSeed
