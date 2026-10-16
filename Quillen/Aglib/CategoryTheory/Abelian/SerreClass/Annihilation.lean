/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.SerreClass.Exact

/-! # Actual annihilated objects in additive Serre localizations -/
@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂ u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
section General
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]
/-- The Serre class is precisely the class of objects killed by localization. -/
lemma isZero_obj_iff (X : C) : IsZero (L.obj X) ↔ P X :=
  ObjectProperty.SerreClassLocalization.isZero_obj_iff L P X

end General
section Canonical
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]
@[instance_reducible]
local instance canonicalQuotientAbelian
    {C₀ : Type u} [Category.{u} C₀] [Abelian C₀]
    (P₀ : ObjectProperty C₀) [P₀.IsSerreClass] :
    Abelian P₀.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P₀.isoModSerre.Q P₀

/-- The canonical quotient annihilates exactly the objects of the Serre class. -/
lemma quotient_isZero_obj_iff (X : C) : IsZero (P.isoModSerre.Q.obj X) ↔ P X :=
  isZero_obj_iff P P.isoModSerre.Q X

end Canonical
end Quillen.SerreLocalization
