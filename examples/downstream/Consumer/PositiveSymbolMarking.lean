/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Quillen.KTheory.Field.PositiveSymbolMarking
public import Quillen.KTheory.LowDegreeScalarAction.DvrSymbols

/-!
# Lower localization input of an ordered Milnor symbol

Transporting the public upper equality through the canonical equivalence of model
universes recovers the original lower DVR unit product over every field.
-/
@[expose] public section

open Quillen Quillen.LowDegreeScalarAction

universe u

namespace Consumer

/-- The original lower DVR input is the canonical lower image of the Milnor pair. -/
theorem milnorPair_loweredUnitProduct (F : Type u) [Field F] (a b : Fˣ) :
    ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1} 2).symm
        (Additive.toMul (Field.milnorToUpperModuleKTwo F (MilnorK.symbol ![a, b]))) =
      DvrSymbols.loweredUnitProduct F a b := by
  rw [Field.milnorToUpperModuleKTwo_pair_eq_unitProduct,
    DvrSymbols.loweredUnitProduct_field]
  rfl

/-- The nontrivial rational sign pair retains the original lower product. -/
theorem rational_loweredPair :
    ((ModuleCat.finiteModuleExactStructure.{0, 0} ℚ).smallKUniverseEquiv.{0, 1} 2).symm
        (Additive.toMul
          (Field.milnorToUpperModuleKTwo ℚ (MilnorK.symbol ![(-1 : ℚˣ), (-1 : ℚˣ)]))) =
      DvrSymbols.loweredUnitProduct ℚ (-1) (-1) :=
  milnorPair_loweredUnitProduct ℚ (-1) (-1)

end Consumer
