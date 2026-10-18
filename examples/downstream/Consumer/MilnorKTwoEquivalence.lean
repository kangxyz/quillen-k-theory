/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Field.MilnorKTwoEquivalence
public import Mathlib.FieldTheory.RatFunc.Basic

/-! Clients using the literal scalar action, positive rank-one class, and original field maps. -/
@[expose] public section

noncomputable section

universe u

namespace MilnorKTwoEquivalenceClients

open Quillen Quillen.Field Quillen.LowDegreeScalarAction

variable (F : Type u) [Field F] [CharZero F]
  (L : Type u) [Field L] [CharZero L] (f : F →+* L)

/-- The inverse recognizes original right-projective classes after genuine base change. -/
theorem recover_originalRightBaseChange
    (z : Additive ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2)) :
    milnorToRightProjectiveKTwo L
        (MilnorK.mapAdd 2 f ((milnorRightProjectiveKTwoEquivCharZero F).symm z)) =
      ((FiniteProjectiveModule.rightBaseChangeExact f).KMap 2).toAdditive z := by
  have h := milnorRightProjectiveKTwoEquivCharZero_naturality f
    ((milnorRightProjectiveKTwoEquivCharZero F).symm z)
  rw [(milnorRightProjectiveKTwoEquivCharZero F).apply_symm_apply] at h
  exact h.symm

omit [CharZero F] in
/-- The original scalar action on the literal positive rank-one class has the negative
ordered-symbol normalization after literal tensor extension. -/
theorem tensorExtension_scalarPositiveCube (a b : Fˣ) :
    upperModuleKTwoMilnorNegativeEquivCharZero L (Additive.ofMul
      ((finiteModuleExtensionExact f).smallKMap.{u + 1} 2
        (ScalarUnit.upperFiniteModuleKOneAction F a (FieldSymbols.positiveUnitKOne F b)))) =
      -MilnorK.symbol ![Units.map f.toMonoidHom a, Units.map f.toMonoidHom b] := by
  change upperModuleKTwoMilnorNegativeEquivCharZero L (Additive.ofMul
    ((finiteModuleExtensionExact f).smallKMap.{u + 1} 2
      (FieldSymbols.unitProduct F a b))) = _
  rw [FieldSymbols.unitProduct_natural, upperModuleKTwoMilnorNegativeEquivCharZero_unitProduct]

/-- The signed inverse reconstructs the negative of an arbitrary actual tensor-extended class. -/
theorem reconstruct_originalUpperBaseChange
    (z : Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2)) :
    milnorToUpperModuleKTwo L
        (MilnorK.mapAdd 2 f (upperModuleKTwoMilnorNegativeEquivCharZero F z)) =
      -(((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) := by
  rw [← upperModuleKTwoMilnorNegativeEquivCharZero_naturality,
    milnorToUpperModuleKTwo_negativeEquivCharZero]

/-- An actual characteristic-zero extension, rather than an assumed abstract naturality law. -/
theorem rationalFunction_scalarPositiveCube (a b : ℚˣ) :
    upperModuleKTwoMilnorNegativeEquivCharZero (RatFunc ℚ) (Additive.ofMul
      ((finiteModuleExtensionExact (algebraMap ℚ (RatFunc ℚ))).smallKMap.{1} 2
        (ScalarUnit.upperFiniteModuleKOneAction ℚ a (FieldSymbols.positiveUnitKOne ℚ b)))) =
      -MilnorK.symbol ![
        Units.map (algebraMap ℚ (RatFunc ℚ)).toMonoidHom a,
        Units.map (algebraMap ℚ (RatFunc ℚ)).toMonoidHom b] :=
  tensorExtension_scalarPositiveCube ℚ (RatFunc ℚ) (algebraMap ℚ (RatFunc ℚ)) a b

end MilnorKTwoEquivalenceClients
