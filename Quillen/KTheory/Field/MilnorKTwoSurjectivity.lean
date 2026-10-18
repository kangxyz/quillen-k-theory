/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Algebra.Group.StableSteinbergKernelGeneration
public import Quillen.KTheory.Field.MilnorKTwoComparison

/-!
# Milnor K2 surjectivity from generated stable-kernel defects

The all-rank stable-Steinberg kernel-generation theorem discharges the rank-two
stage-containment input to the original Milnor-to-Quillen K2 comparison. These
wrappers therefore retain perfectness of the actual stable-fiber fundamental
group as an explicit hypothesis. They assert no such perfectness and add no
injectivity, isomorphism, or positive-marking conclusion.
-/
@[expose] public section

universe u

namespace Quillen.Field

open FiniteProjectiveModule.StableCompletion

variable (F : Type u) [Field F]

/-- The original Milnor-to-right-projective K2 map is surjective when its actual
stable-fiber fundamental group is perfect. The generated kernel theorem supplies
the original rank-two stage containment. -/
theorem milnorToRightProjectiveKTwo_surjective_of_fiberPerfect
    [Group.IsPerfect (StableFiberPiOne F)] :
    Function.Surjective (milnorToRightProjectiveKTwo F) :=
  milnorToRightProjectiveKTwo_surjective F
    (Quillen.StableSteinberg.KernelGeneration.kernel_le_stage_two F)

/-- The original Milnor-to-upper-module K2 map is surjective under perfectness of
the actual stable-fiber fundamental group, using generated rank-two containment. -/
theorem milnorToUpperModuleKTwo_surjective_of_fiberPerfect
    [Group.IsPerfect (StableFiberPiOne F)] :
    Function.Surjective (milnorToUpperModuleKTwo F) :=
  milnorToUpperModuleKTwo_surjective F
    (Quillen.StableSteinberg.KernelGeneration.kernel_le_stage_two F)

/-- For finite fields, the original right-projective K2 group is subsingleton
under the explicit actual stable-fiber perfectness hypothesis. -/
theorem rightProjectiveKTwo_subsingleton_of_finite_of_fiberPerfect
    [Finite F] [Group.IsPerfect (StableFiberPiOne F)] :
    Subsingleton ((FiniteProjectiveModule.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  rightProjectiveKTwo_subsingleton_of_finite F
    (Quillen.StableSteinberg.KernelGeneration.kernel_le_stage_two F)

/-- For finite fields, the original upper-module K2 group is subsingleton under
the explicit actual stable-fiber perfectness hypothesis. -/
theorem upperModuleKTwo_subsingleton_of_finite_of_fiberPerfect
    [Finite F] [Group.IsPerfect (StableFiberPiOne F)] :
    Subsingleton ((ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2) :=
  upperModuleKTwo_subsingleton_of_finite F
    (Quillen.StableSteinberg.KernelGeneration.kernel_le_stage_two F)

end Quillen.Field
