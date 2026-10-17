/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Subcategory

/-! # Actual cokernels of inherited admissible monomorphisms -/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
universe v u

namespace CategoryTheory.ExactCategory.ExactSubcategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- An inherited admissible monomorphism has its actual ambient cokernel in
 the subcategory. This is not closure under arbitrary cokernels. -/
theorem cokernel_mem_of_inflation {X Y : P.FullSubcategory} (f : X ⟶ Y)
    [HasCokernel f.hom] (hf : (exactStructure E P).inflation f) : P (CategoryTheory.Limits.cokernel
      f.hom) := by
  obtain ⟨Z, hZ, p, w, hS⟩ := (inflation_iff E P f).1 hf
  let e := (E.cokernel _ hS).coconePointUniqueUpToIso (cokernelIsCokernel f.hom)
  exact P.prop_of_iso e hZ

end CategoryTheory.ExactCategory.ExactSubcategory
