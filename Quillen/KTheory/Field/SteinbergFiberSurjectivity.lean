/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.Algebra.Group.Hom.CentralLifts
public import Quillen.KTheory.Field.SteinbergFiberComparison

/-!
# Original Steinberg fiber maps under explicit perfectness

If the actual fundamental group of the original stable completion fiber is
perfect, the original Steinberg lift is surjective: it covers the original
stable elementary projection, whose kernel is central. Restriction to the
original kernel, inversion of the original connecting isomorphism, transport
along the specified basepointPath, and the original positive completion
comparison retain surjectivity.

Perfectness of StableFiberPiOne is an explicit, unproved hypothesis in every
statement below. The final target is the original K2 of finite projective
right F-modules. No unconditional perfectness, finite-module codomain,
symbol presentation, or ordered-symbol normalization is asserted.
-/
@[expose] public section

universe u
namespace Quillen.FiniteProjectiveModule.StableCompletion
variable (F : Type u) [Field F]

/-- The original Steinberg lift is surjective under perfectness of its actual fiber target. -/
theorem steinbergToStableFiber_surjective [Group.IsPerfect (StableFiberPiOne F)] :
    Function.Surjective (steinbergToStableFiber F) := by
  apply MonoidHom.surjective_of_central_ker_of_surjective_comp
    (steinbergToStableFiber F) (stableFiberToElementary F)
    (ker_stableFiberToElementary_le_center F)
  rw [steinbergToStableFiber_over]
  exact StableSteinberg.toElementary_surjective F

/-- The same original lift restricts surjectively to the original elementary-map kernel. -/
theorem steinbergKernelToFiberKernel_surjective [Group.IsPerfect (StableFiberPiOne F)] :
    Function.Surjective (steinbergKernelToFiberKernel F) := by
  intro a
  obtain ⟨b, hb⟩ := steinbergToStableFiber_surjective F (a : StableFiberPiOne F)
  have hk : b ∈ (StableSteinberg.toElementary F).ker := by
    change StableSteinberg.toElementary F b = 1
    rw [← steinbergToStableFiber_over]
    change stableFiberToElementary F (steinbergToStableFiber F b) = 1
    rw [hb]
    exact a.property
  exact ⟨⟨b, hk⟩, Subtype.ext hb⟩

/-- The original inverse connecting map and specified basepoint transport preserve surjectivity. -/
theorem steinbergKernelToCompletionPiTwo_surjective [Group.IsPerfect (StableFiberPiOne F)] :
    Function.Surjective (steinbergKernelToCompletionPiTwo F) :=
  (pathTransportMulEquiv (basepointPath F) 1).surjective.comp
    ((imagePiTwoFiberKernelEquiv F).symm.surjective.comp
      (steinbergKernelToFiberKernel_surjective F))

/-- The original map onto right-projective Quillen K2 is surjective under the same hypothesis. -/
theorem steinbergKernelToRightProjectiveKTwo_surjective
    [Group.IsPerfect (StableFiberPiOne F)] :
    Function.Surjective (steinbergKernelToRightProjectiveKTwo F) :=
  (zeroCompletionPositiveKEquiv F 1).surjective.comp
    (steinbergKernelToCompletionPiTwo_surjective F)

end Quillen.FiniteProjectiveModule.StableCompletion
