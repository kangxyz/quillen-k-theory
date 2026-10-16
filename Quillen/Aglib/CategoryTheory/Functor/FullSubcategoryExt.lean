/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Functor equality reflected by a full-subcategory inclusion -/
@[expose] public section
universe u
open CategoryTheory
namespace Quillen
/-- Equality after forgetting a full-subcategory predicate is equality of functors. -/
theorem fullSubcategoryFunctor_ext
    {C D : Type u} [Category.{u} C] [Category.{u} D] {P : ObjectProperty D}
    {F G : C ⥤ P.FullSubcategory} (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  refine CategoryTheory.Functor.ext (fun X => ObjectProperty.FullSubcategory.ext (Functor.congr_obj
    h X)) ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  simpa only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom] using Functor.congr_hom h f

end Quillen

universe v w w'
namespace Quillen.Waldhausen.GilletWaldhausen
/-- Postcomposition by an actual full-subcategory inclusion is injective on functors. -/
theorem fullSubcategory_postcomp_injective {C : Type u} [Category.{v} C]
    (Q : ObjectProperty C) {D : Type w} [Category.{w'} D] :
    Function.Injective (fun F : D ⥤ Q.FullSubcategory ↦ F ⋙ Q.ι) := by
  intro F G h
  refine CategoryTheory.Functor.ext (fun X ↦ ObjectProperty.FullSubcategory.ext
    (Functor.congr_obj h X)) ?_
  intro X Y f
  apply Q.ι.map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_map, Functor.comp_obj] using
    Functor.congr_hom h f

end Quillen.Waldhausen.GilletWaldhausen
