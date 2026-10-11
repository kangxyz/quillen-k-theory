/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassSeed

/-!
# Original fixed-open supported seed consumers

The original zero-level unit loop, whole null cylinder, independent loop/structure times and
coefficient maps are retained. Iteration uses the actual constructed seed. The fixed-open
identity-algebra pullback is not identified with the separately supplied original j.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.SupportedSectionBassSeed
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- At level zero the original realized unit action acts inside the original loop coordinate. -/
theorem original_level_zero_unit (a : Under R) (s t : unitInterval)
    (γ : Path (stagePoint 0 ((boundedFlatAffineSupportedSectionModelFunctor j).obj a))
      (stagePoint 0 ((boundedFlatAffineSupportedSectionModelFunctor j).obj a))) :
    Path.toContinuousMap
        ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level 0 (s, γ)) t =
      stageTransformationTopHomotopy 0
        (F := (boundedFlatAffineSupportedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app a))
        (G := (boundedFlatAffineSupportedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app a))
        (boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a).hom
        (fun A ↦ ((boundedFlatAffineSupportedSectionModelFunctor j).obj
          ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _ (by
            change IsIso ((boundedFlatAffineSupportedDiagramLaurentPullbackUnitIso j a).hom.app A)
            infer_instance)) (s, γ t) := rfl

/-- The actual seed null track keeps every original strict-square cylinder value. -/
theorem original_null_cylinder (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x) =
      (StrictSquare.sourceNullHomotopy
        (boundedFlatAffineSupportedSectionBassSquare j a)).level n (t, x) := rfl

/-- The actual natural seed retains the unchanged original unit and both null-conjugation legs.
-/
theorem original_seed_loop (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap (((boundedFlatAffineSupportedSectionBassSeed j).app a).map n x) t =
      (((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineSupportedSectionBassNullHomotopy j a)).level n (t, x) :=
  boundedFlatAffineSupportedSectionBassSeedMap_apply j a n x t

/-- Structure time and the actual Laurent loop time stay independent in the constructed seed. -/
theorem original_seed_independent_parameters (a : Under R) (n : ℕ)
    (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap (((boundedFlatAffineSupportedSectionBassSeed j).app a).map (n + 1)
        (((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).structureMap n x s)) t =
      Path.toContinuousMap
        ((parameterLooping (boundedFlatAffineSupportedSectionBassCone j a)).structureMap n
          (((boundedFlatAffineSupportedSectionBassSeed j).app a).map n x) s) t := by
  have h := congrArg (fun p ↦ p s) ((boundedFlatAffineSupportedSectionBassSeedMap j a).comm n x)
  exact congrArg (fun γ : Path ((boundedFlatAffineSupportedSectionBassCone j a).point (n + 1))
    ((boundedFlatAffineSupportedSectionBassCone j a).point (n + 1)) ↦ γ t) h

/-- Original coefficient maps commute with the actual supported seed and actual looped cone map.
-/
theorem original_seed_coefficient_square {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSupportedSectionBassSeed j).app a ≫
        parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeMap j f) =
      (boundedFlatAffineSupportedSectionPrespectrumFunctor j).map f ≫
        (boundedFlatAffineSupportedSectionBassSeed j).app b :=
  boundedFlatAffineSupportedSectionBassSeedMap_naturality j f

/-- Every finite transition is the actual iterated image of this one constructed original seed.
-/
theorem original_iterated_seed (n : ℕ) :
    KTheory.Bass.strictDiagramTransition (laurentUnderSquareFunctor R)
        (boundedFlatAffineSupportedSectionBassSeed j) n =
      (KTheory.Bass.strictDiagramIterate (laurentUnderSquareFunctor R) n).map
        (boundedFlatAffineSupportedSectionBassSeed j) := rfl

end Quillen.Tests.SupportedSectionBassSeed
