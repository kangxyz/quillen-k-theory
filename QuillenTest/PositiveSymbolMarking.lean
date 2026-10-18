/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Quillen.KTheory.Field.PositiveSymbolMarking

/-!
# Positive symbol marking consumers

The public field map evaluates on ordered pairs, including a concrete rational pair.
The original right-projective construction remains available before universe transport.
-/

open Quillen Quillen.LowDegreeScalarAction

universe u

namespace QuillenTest.PositiveSymbolMarking

/-- The original right-projective map retains the positive scalar construction. -/
theorem rightProjective_pair (F : Type u) [Field F] (a b : Fˣ) :
    Field.milnorToRightProjectiveKTwo F (MilnorK.symbol ![a, b]) =
      Additive.ofMul (Field.SymbolMarking.scalarClass F a b) :=
  Field.SymbolMarking.milnorToRightProjectiveKTwo_positive_pair F a b

/-- A concrete rational pair evaluates through the public upper map. -/
theorem rational_pair :
    Field.milnorToUpperModuleKTwo ℚ (MilnorK.symbol ![(-1 : ℚˣ), (-1 : ℚˣ)]) =
      Additive.ofMul (FieldSymbols.unitProduct ℚ (-1) (-1)) :=
  Field.milnorToUpperModuleKTwo_pair_eq_unitProduct ℚ (-1) (-1)

end QuillenTest.PositiveSymbolMarking
