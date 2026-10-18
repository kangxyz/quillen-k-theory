/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Quillen.KTheory.Field.SteinbergFiberInjectivity
import Mathlib.Algebra.Field.ZMod

/-!
# Original Steinberg injectivity consumers

The actual original homomorphisms admit cancellation over an arbitrary field and
retain their injectivity and bijectivity over the rational field and fields of
two and three elements.
-/

open Quillen.FiniteProjectiveModule.StableCompletion

universe u

namespace QuillenTest.SteinbergFiberInjectivity

/-- Equality of original right-projective K2 images cancels on the actual kernel. -/
theorem originalKernel_cancel (F : Type u) [Field F]
    (a b : (Quillen.StableSteinberg.toElementary F).ker) :
    steinbergKernelToRightProjectiveKTwo F a = steinbergKernelToRightProjectiveKTwo F b ↔ a = b :=
  (steinbergKernelToRightProjectiveKTwo_injective F).eq_iff

/-- The original stable-fiber homomorphism is bijective over the rational field. -/
theorem rational_originalFiber : Function.Bijective (steinbergToStableFiber ℚ) :=
  steinbergToStableFiber_bijective ℚ

/-- The original kernel map is injective in characteristic two. -/
theorem two_originalKernel :
    Function.Injective (steinbergKernelToRightProjectiveKTwo (ZMod 2)) :=
  steinbergKernelToRightProjectiveKTwo_injective (ZMod 2)

/-- The original stable-fiber homomorphism is bijective in characteristic three. -/
theorem three_originalFiber : Function.Bijective (steinbergToStableFiber (ZMod 3)) :=
  steinbergToStableFiber_bijective (ZMod 3)

end QuillenTest.SteinbergFiberInjectivity
