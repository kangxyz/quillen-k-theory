/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryBasicNull

/-! # The bottom auxiliary open retains the original basic localization null -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open ParameterAuxiliarySupport
universe u
namespace Consumer.ParameterAuxiliaryBasicNull

/-- For an actual open inclusion and bottom auxiliary open, the original null time is unchanged. -/
theorem bottomAuxiliaryNull (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (s : unitInterval) (x : (prespectrum ((fiber U.ι ⊥).obj X)).space n) :
    (prespectrumMap ((ParameterModels.forget (inverseOpen U.ι ⊥).ι).app X)).map n
      (((fullNull U.ι ⊥).homotopy X).level n (s, x)) =
      ((ParameterFullCurrentNull.fullNull U.ι).homotopy X).level n
        (s, (prespectrumMap ((toBasic U.ι ⊥).app X)).map n x) :=
  fullNull_basic_square U.ι ⊥ X n s x

end Consumer.ParameterAuxiliaryBasicNull
