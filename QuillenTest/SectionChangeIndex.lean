/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.SectionChangeIndexLaws

/-! Regression: actual section restriction is a strict natural transformation
of category diagrams. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
open CategoryTheory.SectionChangeIndex
universe u v u' v'
namespace QuillenTest.SectionChangeIndex
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The literal cocartesian section diagram and its strict reindex maps. -/
def diagram (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) : C ⥤ Cat where
  obj c := Cat.of (underCocartesian (Pseudofunctor.Grothendieck.forget F) c)
  map f := (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).toCatHom
  map_id c := Cat.Hom.ext (underCocartesianReindex_id _ c)
  map_comp f g := Cat.Hom.ext (underCocartesianReindex_comp _ f g)

/-- The actual arbitrary change of index, without choosing an inverse to evaluation. -/
def restriction (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (K : C ⥤ D) :
    K ⋙ diagram F ⟶ diagram (pullback F K) where
  app c := (underFunctor F K c).toCatHom
  naturality _ _ f := Cat.Hom.ext (reindex_naturality F K f)

/-- Every component of the strict transformation is the proved original-fiber equivalence. -/
instance restriction_component_equivalence
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (K : C ⥤ D) (c : C) :
    ((restriction F K).app c).toFunctor.IsEquivalence := restriction_isEquivalence F K c

end QuillenTest.SectionChangeIndex
