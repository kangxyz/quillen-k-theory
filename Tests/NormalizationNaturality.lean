/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationNaturality

/-! Consumers of the original binary normalization's two distinct naturality squares. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.Tests.NormalizationNaturality
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}

/-- At an original object, the first-factor square retains its original mapped component. -/
theorem first_factor_component {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F') (A : C) :
    (normalizedWeakTransformation (hF.comp hG) (hF'.comp hG)
      (whiskerRight η G)).app A ≫ (exactNormalizationCompIso hF' hG).hom.app A =
        (exactNormalizationCompIso hF hG).hom.app A ≫
          (Quillen.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)).map
            ((normalizedWeakTransformation hF hF' η).app A) :=
  congrArg (fun e ↦ e.app A) (exactNormalizationCompIso_natural_left hF hF' hG η)

/-- The second-factor square evaluates the original transformation at the normalized object. -/
theorem second_factor_component {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G') (A : C) :
    (normalizedWeakTransformation (hF.comp hG) (hF.comp hG')
      (whiskerLeft F θ)).app A ≫ (exactNormalizationCompIso hF hG').hom.app A =
        (exactNormalizationCompIso hF hG).hom.app A ≫
          (normalizedWeakTransformation hG hG' θ).app
            ((Quillen.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)).obj A) :=
  congrArg (fun e ↦ e.app A) (exactNormalizationCompIso_natural_right hF hG hG' θ)

end Quillen.Tests.NormalizationNaturality
