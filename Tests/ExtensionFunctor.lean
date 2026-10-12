/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.CategoryTheory.ExactCategory.ExtensionFunctorProjection
public import Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact

/-! # Actual exact-functor extension and quotient consumers -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
universe u v u' v'

section Generic
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

example : E.ExtensionTotal ⥤ E'.ExtensionTotal := F.extensionTotalFunctor

example (x : E.ExtensionTotal) :
    F.toFunctor.map (E.extensionQuotientData x).π ≫ (F.extensionQuotientIso x).hom =
      (E'.extensionQuotientData (F.extensionTotalFunctor.obj x)).π :=
  F.extensionQuotientIso_π x

example : E.extensionProjection ⋙ F.mapQ ≅
    F.extensionTotalFunctor ⋙ E'.extensionProjection := F.extensionProjectionIso

example {x y : E.ExtensionTotal} (f : x ⟶ y) :
    F.mapQ.map (E.extensionProjection.map f) ≫ (E'.qIsoOfIso (F.extensionQuotientIso y)).hom =
      (E'.qIsoOfIso (F.extensionQuotientIso x)).hom ≫
        E'.extensionProjection.map (F.extensionTotalFunctor.map f) :=
  F.extensionProjection_naturality f
end Generic

example {R : Type u} {S : Type u'} [Ring R] [Ring S] (f : R →+* S) :
    (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).ExtensionTotal ⥤
      (FiniteProjectiveModule.exactStructure Sᵐᵒᵖ).ExtensionTotal :=
  (FiniteProjectiveModule.rightBaseChangeExact f).extensionTotalFunctor
