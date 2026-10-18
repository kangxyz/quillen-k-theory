/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Algebra.Group.StableSteinberg.Matsumoto.Injectivity
public import Quillen.KTheory.Field.SteinbergFiberInjectivity
public import Quillen.KTheory.Field.MilnorKTwoSurjectivity
public import Quillen.KTheory.Field.PositiveSymbolMarking

/-!
# The original Milnor K2 equivalences in characteristic zero

The existing Milnor maps to original right-projective K2 and upper finite-module
K2 are bijective over fields of characteristic zero. Their additive equivalences
retain the same forward homomorphisms and ordered positive-symbol values.
Both directions commute with the original field-extension maps.

The upper-module negative normalization is explicitly the negative of the
inverse of the positive equivalence. It therefore sends the original positive
ordered unit product to the negative ordered Milnor symbol. No assertion for
infinite fields of positive characteristic is made here.
-/
@[expose] public section

noncomputable section

universe u

namespace Quillen.Field

open FiniteProjectiveModule.StableCompletion
attribute [local instance] StableSteinberg.kernelCommGroup

variable (F : Type u) [Field F] [CharZero F]

/-- Injectivity of the original kernel map and the original kernel-to-K2 map
imply injectivity of their original right-projective composite. -/
theorem milnorToRightProjectiveKTwo_injective_charZero :
    Function.Injective (milnorToRightProjectiveKTwo F) := by
  intro x y h
  apply StableSteinberg.milnorToKernel_injective_charZero F
  apply Additive.toMul.injective
  apply steinbergKernelToRightProjectiveKTwo_injective F
  exact congrArg Additive.toMul h

/-- The original upper-model composite is injective in characteristic zero. -/
theorem milnorToUpperModuleKTwo_injective_charZero :
    Function.Injective (milnorToUpperModuleKTwo F) := by
  intro x y h
  apply milnorToRightProjectiveKTwo_injective_charZero F
  apply Additive.toMul.injective
  apply (rightProjectiveUpperModuleKEquiv F 2).injective
  exact congrArg Additive.toMul h

/-- The original right-projective map is bijective without any fiber-perfectness
or generation premise: the existing theorems supply both. -/
theorem milnorToRightProjectiveKTwo_bijective_charZero :
    Function.Bijective (milnorToRightProjectiveKTwo F) := by
  let := stableFiberPiOne_isPerfect F
  exact ⟨milnorToRightProjectiveKTwo_injective_charZero F,
    milnorToRightProjectiveKTwo_surjective_of_fiberPerfect F⟩

/-- The original upper finite-module map is bijective in characteristic zero. -/
theorem milnorToUpperModuleKTwo_bijective_charZero :
    Function.Bijective (milnorToUpperModuleKTwo F) := by
  let := stableFiberPiOne_isPerfect F
  exact ⟨milnorToUpperModuleKTwo_injective_charZero F,
    milnorToUpperModuleKTwo_surjective_of_fiberPerfect F⟩

/-- The positive right-projective equivalence has the SAME original forward map. -/
def milnorRightProjectiveKTwoEquivCharZero : MilnorK.K F 2 ≃+
    Additive ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  AddEquiv.ofBijective (milnorToRightProjectiveKTwo F)
    (milnorToRightProjectiveKTwo_bijective_charZero F)

/-- The positive upper finite-module equivalence has the SAME original forward map. -/
def milnorUpperModuleKTwoEquivCharZero : MilnorK.K F 2 ≃+
    Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) :=
  AddEquiv.ofBijective (milnorToUpperModuleKTwo F)
    (milnorToUpperModuleKTwo_bijective_charZero F)

/-- The right-projective equivalence retains the literal original homomorphism. -/
theorem milnorRightProjectiveKTwoEquivCharZero_toAddMonoidHom :
    (milnorRightProjectiveKTwoEquivCharZero F).toAddMonoidHom =
      milnorToRightProjectiveKTwo F := rfl

/-- The upper-model equivalence retains the literal original homomorphism. -/
theorem milnorUpperModuleKTwoEquivCharZero_toAddMonoidHom :
    (milnorUpperModuleKTwoEquivCharZero F).toAddMonoidHom =
      milnorToUpperModuleKTwo F := rfl

/-- Applying the positive right-projective equivalence uses the original map. -/
@[simp] theorem milnorRightProjectiveKTwoEquivCharZero_apply (m : MilnorK.K F 2) :
    milnorRightProjectiveKTwoEquivCharZero F m = milnorToRightProjectiveKTwo F m := rfl

/-- Applying the positive upper-model equivalence uses the original map. -/
@[simp] theorem milnorUpperModuleKTwoEquivCharZero_apply (m : MilnorK.K F 2) :
    milnorUpperModuleKTwoEquivCharZero F m = milnorToUpperModuleKTwo F m := rfl

/-- The ordered right-projective symbol retains the original ordered kernel defect. -/
theorem milnorRightProjectiveKTwoEquivCharZero_pair (a b : Fˣ) :
    milnorRightProjectiveKTwoEquivCharZero F (MilnorK.symbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  milnorToRightProjectiveKTwo_pair F a b

/-- The ordered upper-model symbol is the original POSITIVE scalar unit product. -/
theorem milnorUpperModuleKTwoEquivCharZero_pair (a b : Fˣ) :
    milnorUpperModuleKTwoEquivCharZero F (MilnorK.symbol ![a, b]) =
      Additive.ofMul (LowDegreeScalarAction.FieldSymbols.unitProduct F a b) :=
  milnorToUpperModuleKTwo_pair_eq_unitProduct F a b

variable {F} {L : Type u} [Field L] [CharZero L] (f : F →+* L)

/-- The positive right-projective equivalence commutes with original scalar extension. -/
theorem milnorRightProjectiveKTwoEquivCharZero_naturality (m : MilnorK.K F 2) :
    ((FiniteProjectiveModule.rightBaseChangeExact f).KMap 2).toAdditive
        (milnorRightProjectiveKTwoEquivCharZero F m) =
      milnorRightProjectiveKTwoEquivCharZero L (MilnorK.mapAdd 2 f m) :=
  milnorToRightProjectiveKTwo_naturality f m

/-- The positive upper-model equivalence commutes with literal tensor extension. -/
theorem milnorUpperModuleKTwoEquivCharZero_naturality (m : MilnorK.K F 2) :
    ((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        (milnorUpperModuleKTwoEquivCharZero F m) =
      milnorUpperModuleKTwoEquivCharZero L (MilnorK.mapAdd 2 f m) :=
  milnorToUpperModuleKTwo_naturality f m

/-- The inverse right-projective equivalence is natural for the original K-map. -/
theorem milnorRightProjectiveKTwoEquivCharZero_symm_naturality
    (z : Additive ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2)) :
    (milnorRightProjectiveKTwoEquivCharZero L).symm
        (((FiniteProjectiveModule.rightBaseChangeExact f).KMap 2).toAdditive z) =
      MilnorK.mapAdd 2 f ((milnorRightProjectiveKTwoEquivCharZero F).symm z) := by
  have h := milnorRightProjectiveKTwoEquivCharZero_naturality f
    ((milnorRightProjectiveKTwoEquivCharZero F).symm z)
  rw [(milnorRightProjectiveKTwoEquivCharZero F).apply_symm_apply] at h
  exact (congrArg (milnorRightProjectiveKTwoEquivCharZero L).symm h).trans
    ((milnorRightProjectiveKTwoEquivCharZero L).symm_apply_apply _)

/-- The inverse upper-model equivalence is natural for original tensor extension. -/
theorem milnorUpperModuleKTwoEquivCharZero_symm_naturality
    (z : Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2)) :
    (milnorUpperModuleKTwoEquivCharZero L).symm
        (((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      MilnorK.mapAdd 2 f ((milnorUpperModuleKTwoEquivCharZero F).symm z) := by
  have h := milnorUpperModuleKTwoEquivCharZero_naturality f
    ((milnorUpperModuleKTwoEquivCharZero F).symm z)
  rw [(milnorUpperModuleKTwoEquivCharZero F).apply_symm_apply] at h
  exact (congrArg (milnorUpperModuleKTwoEquivCharZero L).symm h).trans
    ((milnorUpperModuleKTwoEquivCharZero L).symm_apply_apply _)

variable (F)

/-- The explicitly NEGATIVE inverse of the positive upper-model equivalence. -/
def upperModuleKTwoMilnorNegativeEquivCharZero :
    Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) ≃+
      MilnorK.K F 2 :=
  (milnorUpperModuleKTwoEquivCharZero F).symm.trans (AddEquiv.neg _)

/-- The negative normalization is literally minus the positive inverse. -/
@[simp] theorem upperModuleKTwoMilnorNegativeEquivCharZero_apply
    (z : Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2)) :
    upperModuleKTwoMilnorNegativeEquivCharZero F z =
      -((milnorUpperModuleKTwoEquivCharZero F).symm z) := rfl

/-- Normalizing the original forward Milnor map gives the negative input. -/
theorem upperModuleKTwoMilnorNegativeEquivCharZero_milnor (m : MilnorK.K F 2) :
    upperModuleKTwoMilnorNegativeEquivCharZero F (milnorToUpperModuleKTwo F m) = -m := by
  change -((milnorUpperModuleKTwoEquivCharZero F).symm
    (milnorUpperModuleKTwoEquivCharZero F m)) = -m
  rw [(milnorUpperModuleKTwoEquivCharZero F).symm_apply_apply]

/-- The original forward map of a negatively normalized class is the negative class. -/
theorem milnorToUpperModuleKTwo_negativeEquivCharZero
    (z : Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2)) :
    milnorToUpperModuleKTwo F (upperModuleKTwoMilnorNegativeEquivCharZero F z) = -z := by
  change milnorUpperModuleKTwoEquivCharZero F
    (-((milnorUpperModuleKTwoEquivCharZero F).symm z)) = -z
  rw [map_neg, (milnorUpperModuleKTwoEquivCharZero F).apply_symm_apply]

/-- The inverse negative normalization is minus the SAME original forward map. -/
theorem upperModuleKTwoMilnorNegativeEquivCharZero_symm_apply (m : MilnorK.K F 2) :
    (upperModuleKTwoMilnorNegativeEquivCharZero F).symm m =
      -(milnorToUpperModuleKTwo F m) := by
  apply (upperModuleKTwoMilnorNegativeEquivCharZero F).injective
  rw [(upperModuleKTwoMilnorNegativeEquivCharZero F).apply_symm_apply, map_neg,
    upperModuleKTwoMilnorNegativeEquivCharZero_milnor, neg_neg]

/-- The actual POSITIVE ordered product normalizes to the NEGATIVE ordered symbol. -/
theorem upperModuleKTwoMilnorNegativeEquivCharZero_unitProduct (a b : Fˣ) :
    upperModuleKTwoMilnorNegativeEquivCharZero F
        (Additive.ofMul (LowDegreeScalarAction.FieldSymbols.unitProduct F a b)) =
      -MilnorK.symbol ![a, b] := by
  rw [← milnorToUpperModuleKTwo_pair_eq_unitProduct F a b,
    upperModuleKTwoMilnorNegativeEquivCharZero_milnor]

variable {F}

/-- The negative normalization commutes with the original upper-model field map. -/
theorem upperModuleKTwoMilnorNegativeEquivCharZero_naturality
    (z : Additive ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2)) :
    upperModuleKTwoMilnorNegativeEquivCharZero L
        (((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      MilnorK.mapAdd 2 f (upperModuleKTwoMilnorNegativeEquivCharZero F z) := by
  change -((milnorUpperModuleKTwoEquivCharZero L).symm
    (((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z)) =
      MilnorK.mapAdd 2 f (-((milnorUpperModuleKTwoEquivCharZero F).symm z))
  rw [milnorUpperModuleKTwoEquivCharZero_symm_naturality, map_neg]

/-- Homomorphism form of the negative normalization's original field-map square. -/
theorem upperModuleKTwoMilnorNegativeEquivCharZero_naturality_hom :
    (upperModuleKTwoMilnorNegativeEquivCharZero L).toAddMonoidHom.comp
        (((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive) =
      (MilnorK.mapAdd 2 f).comp
        (upperModuleKTwoMilnorNegativeEquivCharZero F).toAddMonoidHom := by
  ext z
  exact upperModuleKTwoMilnorNegativeEquivCharZero_naturality f z

/-- The inverse negative normalization also commutes with the original field maps. -/
theorem upperModuleKTwoMilnorNegativeEquivCharZero_symm_naturality (m : MilnorK.K F 2) :
    ((finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        ((upperModuleKTwoMilnorNegativeEquivCharZero F).symm m) =
      (upperModuleKTwoMilnorNegativeEquivCharZero L).symm (MilnorK.mapAdd 2 f m) := by
  rw [upperModuleKTwoMilnorNegativeEquivCharZero_symm_apply,
    upperModuleKTwoMilnorNegativeEquivCharZero_symm_apply, map_neg,
    milnorToUpperModuleKTwo_naturality]

end Quillen.Field
