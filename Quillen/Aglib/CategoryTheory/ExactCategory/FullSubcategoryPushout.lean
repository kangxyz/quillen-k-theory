/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Subcategory

/-!
# Actual admissible pushouts and full exact inclusions

For a zero-containing replete extension-closed property closed under finite
products, the inherited exact inclusion preserves the displayed pushouts along
admissible monomorphisms. The actual ambient objects and maps are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Waldhausen

section GeneralSubcategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The full exact inclusion preserves pushouts along its admissible
monomorphisms. The pushout object stays inside by extension closure. -/
theorem fullSubcategory_map_pushout {A B D T : P.FullSubcategory}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ T} {j : D ⟶ T}
    (hi : (ExactSubcategory.exactStructure E P).inflation i)
    (h : IsPushout i f g j) : IsPushout i.hom f.hom g.hom j.hom := by
  obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff E P i).1 hi
  let : HasPushout i.hom f.hom := E.inflation.hasPushout f.hom
    (E.inflation_of_conflation hS)
  let T₀ : P.FullSubcategory := ⟨pushout i.hom f.hom,
    E.prop_pushout P hS hZ D.property f.hom⟩
  let g₀ : B ⟶ T₀ := P.homMk (pushout.inl _ _)
  let j₀ : D ⟶ T₀ := P.homMk (pushout.inr _ _)
  have h₀ : IsPushout i f g₀ j₀ :=
    IsPushout.of_map_of_faithful P.ι (IsPushout.of_hasPushout i.hom f.hom)
  let e : T₀ ≅ T := h₀.isoIsPushout _ _ h
  apply (IsPushout.of_hasPushout i.hom f.hom).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (P.ι.mapIso e)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    change (g₀ ≫ e.hom).hom = g.hom
    exact congrArg (fun k ↦ k.hom) (h₀.inl_isoIsPushout_hom _ _ h)
  · simp only [Iso.refl_hom, Category.id_comp]
    change (j₀ ≫ e.hom).hom = j.hom
    exact congrArg (fun k ↦ k.hom) (h₀.inr_isoIsPushout_hom _ _ h)

end GeneralSubcategory

end Quillen.Waldhausen
