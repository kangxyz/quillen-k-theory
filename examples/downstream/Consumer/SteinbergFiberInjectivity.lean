/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Quillen.KTheory.Field.SteinbergFiberInjectivity

/-!
# Unique preimages for the original stable-fiber map

A client using only the native defining leaf obtains a unique original stable
Steinberg element above every point of the actual stable-fiber fundamental group.
-/
@[expose] public section

open Quillen.FiniteProjectiveModule.StableCompletion

universe u

namespace Consumer

/-- Every original stable-fiber class has a unique original Steinberg preimage. -/
theorem originalFiber_existsUnique (F : Type u) [Field F] (y : StableFiberPiOne F) :
    ∃! x : Quillen.StableSteinberg.Group F, steinbergToStableFiber F x = y := by
  obtain ⟨x, hx⟩ := (steinbergToStableFiber_bijective F).surjective y
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact (steinbergToStableFiber_injective F) (hz.trans hx.symm)

end Consumer
