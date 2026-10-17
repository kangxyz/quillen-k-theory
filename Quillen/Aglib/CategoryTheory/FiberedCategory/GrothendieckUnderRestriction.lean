/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckUnderSectionMap
public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckUnderComposition
public import Quillen.Aglib.CategoryTheory.FiberedCategory.SectionMap

/-!
# Actual restriction of sections through a pseudonatural transformation

An original section over arrows from `a.right` first restricts to arrows from `a` in
`Under R`. The identity-on-fibers rebracketing and the specified strong transformation
then map its actual total objects and arrows. The resulting section is cocartesian by
the original invertibility criterion, without a chosen inverse evaluation functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckUnderSections
universe u v w w' u' v'
namespace Quillen.CategoryTheory.GrothendieckUnderRestriction
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    (K : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete D) Cat.{v', u'}) (R : C)
    (G : Pseudofunctor (LocallyDiscrete (Under R)) Cat.{v', u'})
    (α : Pseudofunctor.StrongTrans ((Under.forget R ⋙ K).toPseudofunctor.comp F) G)

/-- The specified total map retains the original rebracketing and strong transformation. -/
def totalFunctor :
    Pseudofunctor.Grothendieck (pseudofunctor (K.toPseudofunctor.comp F) R) ⥤
      Pseudofunctor.Grothendieck G :=
  GrothendieckUnderComposition.rebracket K F R ⋙ Pseudofunctor.Grothendieck.map α

/-- The actual total restriction keeps the same coefficient projection. -/
theorem totalFunctor_comp :
    totalFunctor K F R G α ⋙ Pseudofunctor.Grothendieck.forget G =
      Pseudofunctor.Grothendieck.forget (pseudofunctor (K.toPseudofunctor.comp F) R) := rfl

/-- Every original strongly cocartesian arrow remains strongly cocartesian over its same base. -/
theorem totalFunctor_cocartesian {a b : Under R}
    {x y : Pseudofunctor.Grothendieck (pseudofunctor (K.toPseudofunctor.comp F) R)}
    (f : a ⟶ b) (φ : x ⟶ y)
    (h : (Pseudofunctor.Grothendieck.forget
      (pseudofunctor (K.toPseudofunctor.comp F) R)).IsStronglyCocartesian f φ) :
    (Pseudofunctor.Grothendieck.forget G).IsStronglyCocartesian f
      ((totalFunctor K F R G α).map φ) := by
  let := h
  have hx : x.base = a := IsHomLift.domain_eq
    (Pseudofunctor.Grothendieck.forget (pseudofunctor (K.toPseudofunctor.comp F) R)) f φ
  have hy : y.base = b := IsHomLift.codomain_eq
    (Pseudofunctor.Grothendieck.forget (pseudofunctor (K.toPseudofunctor.comp F) R)) f φ
  subst a
  subst b
  obtain rfl : f = φ.base := by
    simpa using IsHomLift.fac (Pseudofunctor.Grothendieck.forget
      (pseudofunctor (K.toPseudofunctor.comp F) R)) f φ
  have : IsIso φ.fiber := GrothendieckCocartesian.isIso_fiber _ φ
  have : IsIso ((GrothendieckUnderComposition.rebracket K F R).map φ).fiber :=
    inferInstanceAs (IsIso φ.fiber)
  have : (Pseudofunctor.Grothendieck.forget
      ((Under.forget R ⋙ K).toPseudofunctor.comp F)).IsStronglyCocartesian
        ((GrothendieckUnderComposition.rebracket K F R).map φ).base
        ((GrothendieckUnderComposition.rebracket K F R).map φ) :=
    GrothendieckCocartesian.of_isIso_fiber
      ((GrothendieckUnderComposition.rebracket K F R).map φ)
  exact GrothendieckCocartesian.map_isStronglyCocartesian α
    ((GrothendieckUnderComposition.rebracket K F R).map φ)

/-- Restrict the actual original section and postcompose its original total maps. -/
def sectionFunctor (a : Under R) :
    underCocartesian (Pseudofunctor.Grothendieck.forget (K.toPseudofunctor.comp F)) a.right ⥤
      underCocartesian (Pseudofunctor.Grothendieck.forget G) a :=
  underFunctor (K.toPseudofunctor.comp F) R a ⋙
    cocartesianPostcompose
      (Pseudofunctor.Grothendieck.forget (pseudofunctor (K.toPseudofunctor.comp F) R))
      (Pseudofunctor.Grothendieck.forget G) (totalFunctor K F R G α)
      (totalFunctor_comp K F R G α) (Under.forget a)
      (fun f φ h => totalFunctor_cocartesian K F R G α f φ h)

end Quillen.CategoryTheory.GrothendieckUnderRestriction
