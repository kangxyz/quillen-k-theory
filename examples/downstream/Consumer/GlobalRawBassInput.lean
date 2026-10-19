/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeed

/-! A client of independent global raw scheme-arrow maps and original forward seeds. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace Consumer.GlobalRawBassInput

/-- Each geometric arrow has an actual raw first-stage map intertwining the original seeds. -/
theorem actual_raw_input_seed {X Y : Scheme.{u}} (g : X ⟶ Y) :
    ∃ F : step Y ⟶ step X,
      Nonempty (Homotopy (transition Y ≫ F)
        (boundedFlatPerfectPrespectrumMap g ≫ transition X)) :=
  ⟨GlobalRawBass.map g, ⟨transitionInputHomotopy g⟩⟩

end Consumer.GlobalRawBassInput
