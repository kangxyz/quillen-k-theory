/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeSeedLoop
public import Quillen.Topology.Prespectrum.LoopTranspose
public import Quillen.Topology.Prespectrum.FiniteLoopWords

/-! # Fixed-order iterated loop strength for the original all-scheme seed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open IteratedLoopStrength FiniteLoopWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- Every fixed-order loop strength retains the original seed with all its loop times. -/
theorem seed_iteratedStrength (A : Track laurent.op coefficient F) (j : ℕ) :
    seed (A.loops j) ≫ iteratedStrength squareFunctor j F = loopMap j (seed A) := by
  induction j with
  | zero => exact Category.comp_id _
  | succ j ih =>
    change seed (A.loops j).loop ≫
      (strengthDiagram squareFunctor _ ≫
        Functor.whiskerRight (iteratedStrength squareFunctor j F) parameterLoopingFunctor) =
      Functor.whiskerRight (loopMap j (seed A)) parameterLoopingFunctor
    rw [← Category.assoc, seed_loop_strength, ← Functor.whiskerRight_comp, ih]

end Quillen.KTheory.Bass.SchemeNaturalSeed
