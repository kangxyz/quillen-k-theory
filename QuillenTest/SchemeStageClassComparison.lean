/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.SchemeStageClassNaturality

/-! The genuine finite correction in negative degree, at stage zero, and on Model inputs. -/
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
    (stableHomotopyFunctor (-(i : ℤ))).map
        ((Telescope.diagramInclusion
          (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
          (currentTransition A) i).app X) ≫
        (currentIteratedStableIso M A X (-(i : ℤ))).hom =
      (finiteStageStableIso M i X (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((Telescope.diagramInclusion
            (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
            (strictDiagramTransition squareFunctor (seed A)) i).app X) :=
  currentIteratedStableIso_inclusion M A i X _

example (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentInitial A).app X) ≫
        (currentIteratedStableIso M A X d).hom =
      (stableHomotopyFunctor d).map ((iteratedInitial A).app X) := by
  have h := currentIteratedStableIso_inclusion M A 0 X d
  rw [finiteStageStableIso_zero_hom] at h
  exact h.trans (Category.id_comp _)

example (N : Scheme.{u}ᵒᵖ ⥤ Model.{w}) (η : M ⟶ N) (i : ℕ) (d : ℤ) :
    (stableHomotopyFunctor d).map
        (((strictDiagramIterate squareFunctor i).map
          (Functor.whiskerRight η prespectrumFunctor)).app X) ≫
        (finiteStageStableIso N i X d).hom =
      (finiteStageStableIso M i X d).hom ≫
        (stableHomotopyFunctor d).map
          (((strictDiagramIterate squareFunctor i).map
            (Functor.whiskerRight η prespectrumFunctor)).app X) :=
  finiteStageStableIso_naturality M N (Functor.whiskerRight η prespectrumFunctor) i X d
