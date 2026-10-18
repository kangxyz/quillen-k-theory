/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeCurrentStageSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack

/-! # Regression on the actual original global-section Laurent action -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.KTheory.Bass Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open NaturalTrack SchemeNaturalSeed NormalizedStageMap
open Quillen.PerfectComplexes.GlobalSchemeLaurentTrack
universe u
namespace QuillenTest.SchemeCurrentStageSquare

/-- The regression uses the original global scalar unit and its proved actual naturality. -/
def originalTrack : Track laurent.op GeometricSeedCospan.coefficient
    diagram.{u} where
  homotopy := homotopy
  naturality := homotopy_naturality

/-- Arbitrary finite-stage adjacency holds on the actual global section diagram. -/
example (i : ℕ) :
    currentTransition originalTrack i ≫ stageMap squareFunctor (i + 1) diagram =
      stageMap squareFunctor i diagram ≫ normalizedTransition originalTrack i :=
  currentTransition_stageMap originalTrack i

/-- The same actual equality holds at each spectrum level on every original input. -/
example (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (((strictDiagramIterate squareFunctor i).obj diagram).obj X).space n) :
    ((stageMap squareFunctor (i + 1) diagram).app X).map n
        (((currentTransition originalTrack i).app X).map n x) =
      ((normalizedTransition originalTrack i).app X).map n
        (((stageMap squareFunctor i diagram).app X).map n x) :=
  congrArg (fun f => (f.app X).map n x) (currentTransition_stageMap originalTrack i)

end QuillenTest.SchemeCurrentStageSquare
