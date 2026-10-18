/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Bass.SchemeIteratedSeedTelescope

/-! # Original finite seed transition regressions -/
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open NormalizedStageMap SchemeIteratedSeedTransition SchemeIteratedSeedTelescope
universe u w
variable {F : Scheme.{u}ᵒᵖ ⥤ Quillen.LoopPrespectrum.{w}}

example (A : Track laurent.op coefficient F) (i : ℕ) :
    strictDiagramTransition squareFunctor (seed A) i ≫ stageMap squareFunctor (i + 1) F =
      stageMap squareFunctor i F ≫ twistedTransition A i := originalTransition_stageMap A i

example (A : Track laurent.op coefficient F) :
    strictDiagramTransition squareFunctor (seed A) 1 ≫ stageMap squareFunctor 2 F =
      stageMap squareFunctor 1 F ≫ twistedTransition A 1 := originalTransition_stageMap A 1

example (A : Track laurent.op coefficient F) :
    strictDiagramTransition squareFunctor (seed A) 2 ≫ stageMap squareFunctor 3 F =
      stageMap squareFunctor 2 F ≫ twistedTransition A 2 := originalTransition_stageMap A 2

example (M : Scheme.{u}ᵒᵖ ⥤ Quillen.Waldhausen.IteratedS.Model.{w}) (i : ℕ)
    (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((stageMap squareFunctor i
      (M ⋙ Quillen.Waldhausen.IteratedS.prespectrumFunctor)).app X) :=
  model_stageMap_stable squareFunctor i M X

example (A : Track laurent.op coefficient F) (i : ℕ) :
    (strictDiagramTransition squareFunctor (seed A) i ≫
        strictDiagramTransition squareFunctor (seed A) (i + 1)) ≫
          stageMap squareFunctor (i + 2) F =
      stageMap squareFunctor i F ≫
        (twistedTransition A i ≫ twistedTransition A (i + 1)) := by
  rw [Category.assoc, originalTransition_stageMap A (i + 1), ← Category.assoc,
    originalTransition_stageMap A i, Category.assoc]

example (M : Scheme.{u}ᵒᵖ ⥤ Quillen.Waldhausen.IteratedS.Model.{w})
    (A : Track laurent.op coefficient (M ⋙ Quillen.Waldhausen.IteratedS.prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((iteratedTwistedTelescopeMap A).app X) :=
  model_iteratedTwistedTelescopeMap_stable M A X

example (A : Track laurent.op coefficient F) (X : Scheme.{u}ᵒᵖ)
    (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj F).obj X).space n) :
    ((iteratedTwistedTelescopeMap A).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj F).obj X)
        (fun j => (strictDiagramTransition squareFunctor (seed A) j).app X) n i (s, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (twistedTransition A j).app X) n i
        (s, ((stageMap squareFunctor i F).app X).map n x) :=
  iteratedTwistedTelescopeMap_cylinder A X n i s x
