/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Resolution.Finite

/-! # Transporting actual finite admissible resolutions along isomorphisms -/
@[expose] public section

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure.FiniteResolution
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {E : ExactStructure C} {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms]

/-- Change only the augmentation target of a finite resolution, using an
actual isomorphism. Every resolving term and every syzygy is retained. -/
def ofIso {X Y : C} (e : X ≅ Y) : E.FiniteResolution P X → E.FiniteResolution P Y
  | .of_mem hX => .of_mem (P.prop_of_iso e hX)
  | .step S hS hP R =>
    let T := ShortComplex.mk S.f (S.g ≫ e.hom) (by simp)
    .step T (E.iso_closed (S := S) (T := T) (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by simp [T]) (by simp [T])) hS) hP R

@[simp]
theorem length_ofIso {X Y : C} (e : X ≅ Y) (T : E.FiniteResolution P X) :
    (T.ofIso e).length = T.length := by
  cases T <;> rfl

end CategoryTheory.ExactCategory.ExactStructure.FiniteResolution
