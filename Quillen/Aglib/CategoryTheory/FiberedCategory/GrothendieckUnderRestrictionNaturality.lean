/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckUnderRestriction

/-!
# Coefficient naturality of the original section restriction

Restricting the actual section and then applying the specified total functor commutes
literally with the original coefficient reindexing. All fibers and vertical maps remain
those of the original strong transformation.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckUnderSections
universe u v w w' u' v'
namespace Quillen.CategoryTheory.GrothendieckUnderRestriction
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    (K : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (R : C)
    (G : Pseudofunctor (LocallyDiscrete (Under R)) Cat.{v', u'})
    (α : Pseudofunctor.StrongTrans ((Under.forget R ⋙ K).toPseudofunctor.comp F) G)

/-- The unchanged coefficient reindexing commutes with the actual section restriction. -/
theorem sectionFunctor_naturality {a b : Under R} (f : a ⟶ b) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget (K.toPseudofunctor.comp F))
        f.right ⋙ sectionFunctor K F R G α b =
      sectionFunctor K F R G α a ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget G) f := rfl

end Quillen.CategoryTheory.GrothendieckUnderRestriction
