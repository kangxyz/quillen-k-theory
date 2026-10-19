/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryBasicNull

/-! # Equality of the original auxiliary and basic null maps on their whole time domain -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open ParameterAuxiliarySupport
universe u
namespace QuillenTest.ParameterAuxiliaryBasicNull

/-- The entire original time-domain maps agree, including all interior points and endpoints. -/
theorem fullNull_level_square {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (((fullNull f T).homotopy X).postcomp
      (prespectrumMap ((ParameterModels.forget (inverseOpen f T).ι).app X))).level n =
      (Homotopy.precomp (prespectrumMap ((toBasic f T).app X))
        ((ParameterFullCurrentNull.fullNull f).homotopy X)).level n := by
  apply ContinuousMap.ext
  intro p
  exact fullNull_basic_square f T X n p.1 p.2

end QuillenTest.ParameterAuxiliaryBasicNull
