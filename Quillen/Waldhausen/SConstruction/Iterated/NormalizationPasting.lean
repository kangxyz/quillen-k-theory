/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality

/-!
# Actual relative pasting for binary normalization squares

These comparisons use the original zero-preserving transformation tracks. In particular they
introduce no second normalization of the already normalized functors. The binary squares are
proved categorical equalities; their relative realization is supplied by the actual triangles.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u v
namespace Quillen.Waldhausen.IteratedS

section Original
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G G' H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hG' : IsExact W.cof W.weq V.cof V.weq G')
  (hH : IsExact W.cof W.weq V.cof V.weq H)

/-- Equal composites compare the original based tracks, without an additional normalization. -/
def originalPrespectrumPastingHomotopy
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0G' : G'.obj W.zero = V.zero) (h0H : H.obj W.zero = V.zero)
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (hcomp : η ≫ θ = η' ≫ θ') :
    ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).trans
      (originalPrespectrumTransformationHomotopy W V hG hH h0G h0H θ hθ)).RelHomotopy
      ((originalPrespectrumTransformationHomotopy W V hF hG' h0F h0G' η' hη').trans
        (originalPrespectrumTransformationHomotopy W V hG' hH h0G' h0H θ' hθ')) := by
  have he : originalPrespectrumTransformationHomotopy W V hF hH h0F h0H (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) =
    originalPrespectrumTransformationHomotopy W V hF hH h0F h0H (η' ≫ θ')
      (fun A ↦ V.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
    congr 1
  have J := originalPrespectrumTransformationCompositionHomotopy W V hF hG' hH
    h0F h0G' h0H η' θ' hη' hθ'
  rw [← he] at J
  exact (originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
    h0F h0G h0H η θ hη hθ).symm.trans J
end Original

section Binary
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}

/-- In the original universes, postwhiskering preserves the complete based homotopy track. -/
theorem originalPrespectrumTransformationHomotopy_postcomp_level
    {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (h0F : F.obj W.zero = V.zero) (h0F' : F'.obj W.zero = V.zero)
    (h0G : G.obj V.zero = U.zero) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W U (hF.comp hG) (hF'.comp hG)
      ((congrArg G.obj h0F).trans h0G) ((congrArg G.obj h0F').trans h0G)
      (whiskerRight η G) (fun A ↦ hG.weak _ (hη A))).level n =
      ((originalPrespectrumTransformationHomotopy W V hF hF' h0F h0F' η hη).postcomp
        (originalPrespectrumMap V U hG h0G)).level n := by
  exact prespectrumTransformationHomotopy_postcomp_level
    (F := modelMap W V hF h0F) (G := modelMap W V hF' h0F')
    (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (fun A ↦ hη (AsSmall.down.obj A)) (modelMap V U hG h0G) n

/-- In the original universes, prewhiskering preserves the complete based homotopy track. -/
theorem originalPrespectrumTransformationHomotopy_precomp_level
    {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G')
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj V.zero = U.zero)
    (h0G' : G'.obj V.zero = U.zero) (θ : G ⟶ G')
    (hθ : ∀ A, U.weq (θ.app A)) (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W U (hF.comp hG) (hF.comp hG')
      ((congrArg G.obj h0F).trans h0G) ((congrArg G'.obj h0F).trans h0G')
      (whiskerLeft F θ) (fun A ↦ hθ (F.obj A))).level n =
      (Quillen.LoopPrespectrum.Homotopy.precomp (originalPrespectrumMap W V hF h0F)
        (originalPrespectrumTransformationHomotopy V U hG hG' h0G h0G' θ hθ)).level n := by
  exact prespectrumTransformationHomotopy_precomp_level
    (F := modelMap V U hG h0G) (G := modelMap V U hG' h0G')
    (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
    (fun A ↦ hθ (AsSmall.down.obj A)) (modelMap W V hF h0F) n

/-- The original first-factor normalization square has an actual whole relative pasting.
Its first route normalizes the whiskered transformation and then compares composites; its second
route compares composites and then postwhiskers the normalized transformation. -/
def exactNormalizationLeftPasting {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) :=
  originalPrespectrumPastingHomotopy W U
    (hF.comp hG).rebase (hF'.comp hG).rebase
    (hF.rebase.comp hG.rebase) (hF'.rebase.comp hG.rebase)
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (Quillen.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (Quillen.rebaseFunctor_obj_base _ _ _ _)).trans
      (Quillen.rebaseFunctor_obj_base _ _ _ _))
    ((congrArg (Quillen.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (Quillen.rebaseFunctor_obj_base _ _ _ _)).trans
      (Quillen.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation (hF.comp hG) (hF'.comp hG) (whiskerRight η G))
    (exactNormalizationCompIso hF' hG).hom
    (exactNormalizationCompIso hF hG).hom
    (whiskerRight (normalizedWeakTransformation hF hF' η)
      (Quillen.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)))
    (normalizedWeakTransformation_weak _ _ _ (fun A ↦ hG.weak _ (hη A)))
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (fun A ↦ hG.rebase.weak _ (normalizedWeakTransformation_weak hF hF' η hη A))
    (exactNormalizationCompIso_natural_left hF hF' hG η)

/-- The original second-factor normalization square has an actual whole relative pasting.
Both routes retain the original normalized transformation and the actual binary comparison. -/
def exactNormalizationRightPasting {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G')
    (hθ : ∀ A, U.weq (θ.app A)) :=
  originalPrespectrumPastingHomotopy W U
    (hF.comp hG).rebase (hF.comp hG').rebase
    (hF.rebase.comp hG.rebase) (hF.rebase.comp hG'.rebase)
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (Quillen.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (Quillen.rebaseFunctor_obj_base _ _ _ _)).trans
      (Quillen.rebaseFunctor_obj_base _ _ _ _))
    ((congrArg (Quillen.rebaseFunctor G' V.zero U.zero
      ((hG'.zero V.isZero).iso U.isZero)).obj
      (Quillen.rebaseFunctor_obj_base _ _ _ _)).trans
      (Quillen.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation (hF.comp hG) (hF.comp hG') (whiskerLeft F θ))
    (exactNormalizationCompIso hF hG').hom
    (exactNormalizationCompIso hF hG).hom
    (whiskerLeft (Quillen.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
      (normalizedWeakTransformation hG hG' θ))
    (normalizedWeakTransformation_weak _ _ _ (fun A ↦ hθ (F.obj A)))
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _A ↦ normalizedWeakTransformation_weak hG hG' θ hθ _)
    (exactNormalizationCompIso_natural_right hF hG hG' θ)
end Binary

end Quillen.Waldhausen.IteratedS
