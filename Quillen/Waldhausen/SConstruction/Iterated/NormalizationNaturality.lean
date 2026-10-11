/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.ExactCoherence

/-!
# Naturality of the original binary zero normalization

The displayed comparison is the actual rebasing isomorphism used in the binary prespectrum
composition homotopy. Its two naturality squares retain the original transformations and
whiskering maps. These categorical identities do not by themselves assert spectral pasting.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}

/-- The actual binary comparison between the canonical zero-normalized functors. -/
def exactNormalizationCompIso {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G) :
    Quillen.rebaseFunctor (F ⋙ G) W.zero U.zero (((hF.comp hG).zero W.isZero).iso U.isZero) ≅
      Quillen.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero) ⋙
        Quillen.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero) :=
  (Quillen.rebaseFunctorIso (F ⋙ G) W.zero U.zero
    (((hF.comp hG).zero W.isZero).iso U.isZero)).symm ≪≫
    isoWhiskerRight (Quillen.rebaseFunctorIso F W.zero V.zero
      ((hF.zero W.isZero).iso V.isZero)) G ≪≫
    isoWhiskerLeft _ (Quillen.rebaseFunctorIso G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero))

private theorem homotopy_level_cast {X Y : Quillen.LoopPrespectrum}
    {f g g' : X ⟶ Y} (e : g = g')
    (p : Quillen.LoopPrespectrum.Homotopy f g = Quillen.LoopPrespectrum.Homotopy f g')
    (H : Quillen.LoopPrespectrum.Homotopy f g) (n : ℕ) :
    (p.mp H).level n = H.level n := by
  subst g'
  rfl

/-- Every full level track of the existing binary homotopy is induced by this exact iso. -/
theorem exactOriginalPrespectrumMapCompHomotopy_level {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G) (n : ℕ) :
    (exactOriginalPrespectrumMapCompHomotopy W V U hF hG).level n =
      (originalPrespectrumTransformationHomotopy W U (hF.comp hG).rebase
        (hF.rebase.comp hG.rebase) (Quillen.rebaseFunctor_obj_base _ _ _ _)
        ((congrArg (Quillen.rebaseFunctor G V.zero U.zero
          ((hG.zero V.isZero).iso U.isZero)).obj
          (Quillen.rebaseFunctor_obj_base _ _ _ _)).trans
          (Quillen.rebaseFunctor_obj_base _ _ _ _))
        (exactNormalizationCompIso hF hG).hom
        (fun _A ↦ U.weq_iso _ inferInstance)).level n := by
  simp only [exactOriginalPrespectrumMapCompHomotopy, exactNormalizationCompIso]
  apply homotopy_level_cast (originalPrespectrumMap_comp W V U hF.rebase hG.rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _))

/-- Postwhiskering a transformation commutes with the actual binary normalization. -/
theorem exactNormalizationCompIso_natural_left {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F') :
    normalizedWeakTransformation (hF.comp hG) (hF'.comp hG) (whiskerRight η G) ≫
        (exactNormalizationCompIso hF' hG).hom =
      (exactNormalizationCompIso hF hG).hom ≫
        whiskerRight (normalizedWeakTransformation hF hF' η)
          (Quillen.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)) := by
  ext A
  simp [exactNormalizationCompIso, normalizedWeakTransformation, Category.assoc,
    ← Functor.map_comp]

/-- Prewhiskering a transformation commutes with the actual binary normalization. -/
theorem exactNormalizationCompIso_natural_right {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G') :
    normalizedWeakTransformation (hF.comp hG) (hF.comp hG') (whiskerLeft F θ) ≫
        (exactNormalizationCompIso hF hG').hom =
      (exactNormalizationCompIso hF hG).hom ≫
        whiskerLeft (Quillen.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
          (normalizedWeakTransformation hG hG' θ) := by
  ext A
  simp [exactNormalizationCompIso, normalizedWeakTransformation, Category.assoc]

end Quillen.Waldhausen.IteratedS
