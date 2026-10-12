/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.GroupCompletion.FullyFaithful
public import Quillen.CategoryTheory.GroupCompletion.LocalizationFunctoriality

/-!
# Equivalences on the original localization

A fully faithful, essentially surjective equivariant functor induces an
equivalence on Grayson's original localization when its lineators are invertible.
The functor is exactly `Localization.map`: its representatives retain their
denominators and first-coordinate maps. No equivariant inverse, braiding, or
groupoid hypothesis is needed.
-/

@[expose] public section

noncomputable section

universe u v u₁ v₁ u₂ v₂

open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear

namespace Quillen.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

instance mapPair_faithful [F.Faithful] : (mapPair (C := C) F).Faithful where
  map_injective {X Y} f g h := by
    change (f.1, F.map f.2) = (g.1, F.map g.2) at h
    exact Prod.ext (Prod.mk.inj h).1 (F.map_injective (Prod.mk.inj h).2)

instance mapPair_full [F.Full] : (mapPair (C := C) F).Full where
  map_surjective f := by
    refine ⟨(f.1, F.preimage f.2), ?_⟩
    apply Prod.ext
    · rfl
    · exact F.map_preimage f.2

/-- Essential surjectivity descends without any invertibility assumption on
the lineators: lift an original isomorphism with the denominator fixed. -/
instance map_essSurj [F.EssSurj] : (map (C := C) F).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F Y.obj.2
    exact ⟨⟨(Y.obj.1, X)⟩,
      ⟨(ActionLocalization.ofFunctor (C := C)).mapIso ((Iso.refl Y.obj.1).prod e)⟩⟩

variable [∀ (s : C) (X : D), IsIso (μₗ F s X)]

instance mapPair_lineator_isIso (s : C) (X : C × D) :
    IsIso (μₗ (mapPair F) s X) := by
  apply (isIso_prod_iff C E).2
  constructor
  · change IsIso (𝟙 (s ⊗ X.1))
    infer_instance
  · change IsIso (μₗ F s X.2)
    infer_instance

/-- Faithfulness of the exact quotient functor follows by reflecting the
denominator relation through the original faithful functor. -/
instance map_faithful [F.Faithful] : (map (C := C) F).Faithful :=
  ActionLocalization.mapFunctor_faithful (mapPair F)

/-- Fullness lifts the second-coordinate representative by the inverse
lineator, leaving the denominator and first-coordinate map unchanged. -/
instance map_full [F.Full] : (map (C := C) F).Full :=
  ActionLocalization.mapFunctor_full (mapPair F)

instance map_isEquivalence [F.Full] [F.Faithful] [F.EssSurj] :
    (map (C := C) F).IsEquivalence where

/-- The equivalence induced by the original equivariant functor on Grayson's
localization; its forward functor is exactly `Localization.map F`. -/
def mapEquivalence [F.Full] [F.Faithful] [F.EssSurj] :
    Localization C D ≌ Localization C E :=
  (map F).asEquivalence

@[simp]
lemma mapEquivalence_functor [F.Full] [F.Faithful] [F.EssSurj] :
    (mapEquivalence (C := C) F).functor = map F := rfl

end Quillen.GroupCompletion.Localization
