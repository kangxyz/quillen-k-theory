/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.SchemeStageInclusionComparison

/-! Original finite inclusions in negative degree and at the independent initial stage. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
universe u w
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
  (X : Scheme.{u}ᵒᵖ)

example (i : ℕ) :
    IsIso ((stableHomotopyFunctor (-(i : ℤ))).map
      ((Telescope.diagramInclusion
        (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
        (currentTransition A) i).app X)) ↔
    IsIso ((stableHomotopyFunctor (-(i : ℤ))).map
      ((Telescope.diagramInclusion
        (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
        (strictDiagramTransition squareFunctor (seed A)) i).app X)) :=
  model_currentInclusion_isIso_iff_iteratedInclusion M A i X _

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map ((currentInitial A).app X)) ↔
      IsIso ((stableHomotopyFunctor d).map ((iteratedInitial A).app X)) :=
  model_currentInclusion_isIso_iff_iteratedInclusion M A 0 X d

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion
        (fun j => normalized squareFunctor j (M ⋙ prespectrumFunctor))
        (normalizedTransition A) 2).app X)) ↔
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion
        (fun j => normalized squareFunctor j (M ⋙ prespectrumFunctor))
        (twistedTransition A) 2).app X)) :=
  model_normalizedInclusion_isIso_iff_twistedInclusion M A 2 X d
