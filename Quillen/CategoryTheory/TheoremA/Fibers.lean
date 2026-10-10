/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.Resolution
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Strict fibers of the Theorem A resolution

The target projection of the comma resolution has the comma category `(F ↓ d)`
as its categorical fiber. This file constructs the equivalence with mathlib's
`Functor.Fiber`, whose arrows are restricted to those mapping to the identity.
This is a categorical fiber statement, not yet a topological homotopy-fiber
statement.
-/
@[expose] public section


noncomputable section

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (d : D)

/-- The comma category included in the strict categorical fiber. -/
def toFiber : CostructuredArrow F d ⥤ (targetProjection F).Fiber d :=
  CategoryTheory.Functor.Fiber.inducedFunctor (fiberInclusion_target F d)

@[simp]
theorem toFiber_inclusion :
    toFiber F d ⋙ CategoryTheory.Functor.Fiber.fiberInclusion = fiberInclusion F d := rfl

instance : (toFiber F d).Faithful where
  map_injective {X Y} f g h := by
    apply CostructuredArrow.hom_ext
    exact congrArg (fun k ↦ k.val.left) h

instance : (toFiber F d).Full where
  map_surjective {X Y} f := by
    have := f.property
    have hf : f.val.right = 𝟙 d := by
      have h := IsHomLift.fac (targetProjection F) (𝟙 d) f.val
      change (targetProjection F).map f.val = 𝟙 d
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h.symm
    refine ⟨CostructuredArrow.homMk f.val.left ?_, ?_⟩
    · have h := f.val.w
      change F.map f.val.left ≫ Y.hom = X.hom ≫ f.val.right at h
      simpa only [hf, Category.comp_id] using h
    · apply Subtype.ext
      exact Comma.hom_ext _ _ rfl hf.symm

instance : (toFiber F d).EssSurj := by
  apply CategoryTheory.Functor.essSurj_of_surj
  rintro ⟨⟨c, e, h⟩, he⟩
  change e = d at he
  cases he
  exact ⟨CostructuredArrow.mk h, rfl⟩

instance : (toFiber F d).IsEquivalence where

/-- The strict fiber of the resolution over `d` is precisely `(F ↓ d)`. -/
def commaFiberEquivalence : CostructuredArrow F d ≌ (targetProjection F).Fiber d :=
  (toFiber F d).asEquivalence

end Quillen.TheoremA
