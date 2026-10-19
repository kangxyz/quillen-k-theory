/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputMixedDesc

/-! A downstream client uses the exact original whole Y descent surface. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputMixed
open GlobalBassEvaluation GlobalSectionChangeIndex

/-- Original raw Laurent pullback acts on the entire old descent surface at unchanged clocks. -/
theorem original_post_desc_square {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputMixedDesc.postSquareParameter g) n ((r, s), x) =
    (prespectrumMap (evaluationRawMap (laurent.map g))).map n
      ((descPasting Y).toSquare.level n (r, (s, x))) :=
  InputMixedDesc.post_square_parameter_native g n r s x

end Consumer.GlobalBassEvaluationInputMixed
