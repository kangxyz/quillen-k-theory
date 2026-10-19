/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedReindexForgetComposition
public import Quillen.Aglib.CategoryTheory.Functor.EqToHomWhiskerSquare

/-! # The complete supported reindex transport after actual inclusion

The actual two-edge forget comparisons are identities as entire natural transformations.
The original supported square therefore retains its ambient whiskered equality transport
before any component is taken.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation

/-- The whole two-edge forget comparison is the identity transformation. -/
theorem supportedReindexRoute_forget_hom {A B C : Scheme.OpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    eqToHom (supportedReindexRoute_forget f g) =
      𝟙 ((supported (X := op C.obj.right) C.obj.hom).ι ⋙
        ((globalModel.map g.hom.right.op).functor ⋙
          (globalModel.map f.hom.right.op).functor)) := rfl

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The entire original supported square retains the entire ambient equality transport. -/
theorem supportedReindexEquality_forget_whisker :
    whiskerRight (eqToHom (supportedReindexInputSquare p q a b h))
        (supported (X := op C.obj.right) C.obj.hom).ι =
      whiskerLeft (supported (X := op B.obj.right) B.obj.hom).ι
        (eqToHom (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
          (congrArg (fun f : C ⟶ B => f.hom.right) h))) := by
  have he := Functor.eqToHom_whisker_square
    (supported (X := op B.obj.right) B.obj.hom).ι
    (supported (X := op C.obj.right) C.obj.hom).ι
    ((supportedPairModelMap p).functor ⋙ (supportedPairModelMap a).functor)
    ((supportedPairModelMap b).functor ⋙ (supportedPairModelMap q).functor)
    ((globalModel.map p.hom.right.op).functor ⋙ (globalModel.map a.hom.right.op).functor)
    ((globalModel.map b.hom.right.op).functor ⋙ (globalModel.map q.hom.right.op).functor)
    (supportedReindexInputSquare p q a b h)
    (globalReindexInputSquare p.hom.right q.hom.right a.hom.right b.hom.right
      (congrArg (fun f : C ⟶ B => f.hom.right) h))
    (supportedReindexRoute_forget a p) (supportedReindexRoute_forget q b)
  rw [supportedReindexRoute_forget_hom q b, supportedReindexRoute_forget_hom a p] at he
  exact (Category.comp_id _).symm.trans (he.trans (Category.id_comp _))

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
