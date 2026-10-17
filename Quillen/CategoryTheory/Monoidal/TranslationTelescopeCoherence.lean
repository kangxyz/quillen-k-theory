/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Monoidal.TensorFunctor.Associativity
public import Quillen.CategoryTheory.Monoidal.TranslationTelescope
public import Quillen.Aglib.CategoryTheory.Grothendieck.EndofunctorTelescopeComposition

/-! # Original unit and composition isomorphisms for telescope translations -/
@[expose] public section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original left unitor gives the unit isomorphism on the unlifted telescope. -/
def originalUnitIso (e : C) :
    EndofunctorTelescope.map (leftStep e (𝟙_ C)) ≅
      𝟭 (EndofunctorTelescope.Model (tensorRight e)) :=
  EndofunctorTelescope.mapNatIso (M := 𝟭 C) (leftStep e (𝟙_ C)) (𝟙 (tensorRight e))
    (leftUnitorNatIso C) (by
      intro X
      dsimp [leftStep]
      simp only [Category.comp_id]
      rw [leftUnitor_tensor_hom]
      simp) ≪≫
    eqToIso (EndofunctorTelescope.map_identity (tensorRight e))

/-- Telescope translation composition is governed by the original pentagon. -/
def originalTensorIso (e P Q : C) :
    EndofunctorTelescope.map (leftStep e (P ⊗ Q)) ≅
      EndofunctorTelescope.map (leftStep e Q) ⋙
        EndofunctorTelescope.map (leftStep e P) :=
  EndofunctorTelescope.mapNatIso (leftStep e (P ⊗ Q))
    (EndofunctorTelescope.composeStep (leftStep e Q) (leftStep e P))
    (leftTensorIso P Q) (by
      intro X
      dsimp [leftStep, leftTensorIso, EndofunctorTelescope.composeStep]
      exact pentagon P Q X e) ≪≫
    eqToIso (EndofunctorTelescope.map_composeStep _ _)

/-- Unit translation on the actual common-universe telescope. -/
def leftTranslationUnit (e : C) : leftTranslation e (𝟙_ C) ≅ 𝟭 (Model e) :=
  Functor.isoWhiskerLeft (modelEquivalence e).functor
      (Functor.isoWhiskerRight (originalUnitIso e) (modelEquivalence e).inverse) ≪≫
    (modelEquivalence e).unitIso.symm

/-- Composition on the actual common-universe telescope, with its original associator. -/
def leftTranslationTensor (e P Q : C) :
    leftTranslation e (P ⊗ Q) ≅ leftTranslation e Q ⋙ leftTranslation e P :=
  Functor.isoWhiskerLeft (modelEquivalence e).functor
      (Functor.isoWhiskerRight (originalTensorIso e P Q) (modelEquivalence e).inverse) ≪≫
    Functor.isoWhiskerLeft ((modelEquivalence e).functor ⋙
      EndofunctorTelescope.map (leftStep e Q))
      (Functor.isoWhiskerRight (modelEquivalence e).counitIso.symm
        (EndofunctorTelescope.map (leftStep e P) ⋙ (modelEquivalence e).inverse))

/-- An actual isomorphism of the translating objects induces its original telescope isomorphism. -/
def leftTranslationIso (e : C) {P Q : C} (f : P ≅ Q) :
    leftTranslation e P ≅ leftTranslation e Q :=
  Functor.isoWhiskerLeft (modelEquivalence e).functor
    (Functor.isoWhiskerRight
      (EndofunctorTelescope.mapNatIso (leftStep e P) (leftStep e Q)
        ((curriedTensor C).mapIso f) (by
          intro X
          dsimp [leftStep]
          exact associator_naturality_left f.hom X e))
      (modelEquivalence e).inverse)

end Quillen.TranslationTelescope
