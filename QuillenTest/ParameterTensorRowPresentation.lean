/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorRowPresentation

/-! Actual ambient and supported forward seeds retain the original independent loop coordinate. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterTensorRowPresentation

/-- The ambient proper-row seed keeps the original null-conjugated time at every stage. -/
theorem ambient_seed_coordinate (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterModels.ambient Q ⋙ prespectrumFunctor)).obj X).space n) (t : unitInterval) :
    Path.toContinuousMap
      ((SchemeModelRowSeed.forward (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
        i X).map n x) t =
      (ModelDiagramRowRefinement.comparison squareFunctor i (ParameterModels.ambient Q) X).map n
        (Path.toContinuousMap (((SchemeNaturalSeed.seed
          (SchemeNaturalSeed.stageTrack
            (ParameterLaurentTrack.ambientTrack Q) i)).app X).map n x) t) :=
  congrArg (fun a => Path.toContinuousMap (a.map n x) t)
    (SchemeModelRowSeed.forward_eq_seed (ParameterModels.ambient Q)
      (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X)

/-- The supported seed uses the supported original track and null at the identical loop time. -/
theorem supported_seed_coordinate {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterModels.supported f ⋙ prespectrumFunctor)).obj X).space n) (t : unitInterval) :
    Path.toContinuousMap
      ((SchemeModelRowSeed.forward (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
        i X).map n x) t =
      (ModelDiagramRowRefinement.comparison squareFunctor i (ParameterModels.supported f) X).map n
        (Path.toContinuousMap (((SchemeNaturalSeed.seed
          (SchemeNaturalSeed.stageTrack
            (ParameterLaurentTrack.supportedTrack f) i)).app X).map n x) t) :=
  congrArg (fun a => Path.toContinuousMap (a.map n x) t)
    (SchemeModelRowSeed.forward_eq_seed (ParameterModels.supported f)
      (ParameterLaurentTrack.supportedUnit f)
      (ParameterLaurentTrack.supportedUnit_naturality f) i X)

end QuillenTest.ParameterTensorRowPresentation
