/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationNaturality

/-!
# Associativity of the original chosen-zero normalization

For three exact functors between Waldhausen categories, the two composites of the actual
binary normalization isomorphisms agree, with the functor associator displayed explicitly.
The proof expands `exactNormalizationCompIso` from `NormalizationNaturality` and cancels the
original normalization factors. These are the normalization faces of iterated geometric
composition diagrams; no additional coherence hypothesis is required.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u v
namespace Quillen.Waldhausen.IteratedS

variable {C D E K : Type u}
  [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} K]
  {W : Structure C} {V : Structure D} {U : Structure E} {T : Structure K}
  {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ K}

/-- The actual binary zero-normalization isomorphisms satisfy their three-factor coherence.
No replacement normalization or coherence premise is used. -/
theorem exactNormalizationCompIso_associativity
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hH : IsExact U.cof U.weq T.cof T.weq H) :
    (exactNormalizationCompIso hF (hG.comp hH)).hom ≫
      whiskerLeft
        (Quillen.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
        (exactNormalizationCompIso hG hH).hom =
    (exactNormalizationCompIso (hF.comp hG) hH).hom ≫
      whiskerRight (exactNormalizationCompIso hF hG).hom
        (Quillen.rebaseFunctor H U.zero T.zero ((hH.zero U.isZero).iso T.isZero)) ≫
      (Functor.associator
        (Quillen.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
        (Quillen.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero))
        (Quillen.rebaseFunctor H U.zero T.zero ((hH.zero U.isZero).iso T.isZero))).hom := by
  ext A
  simp [exactNormalizationCompIso, Category.assoc, ← Functor.map_comp]
  rfl

end Quillen.Waldhausen.IteratedS
