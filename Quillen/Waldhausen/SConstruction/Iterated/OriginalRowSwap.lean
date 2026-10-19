/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopFunctor
public import Quillen.Waldhausen.SConstruction.Iterated.RowSwapTransformation
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationNaturality

/-!
# Original-universe row interchange and the exact normalization tracks

The actual row transpose commutes with the unchanged original exact-functor spectrum maps,
weak-transformation tracks, and binary normalization homotopy. All original small-model and
chosen-zero normalizations are retained. The binary comparison is handled through its proved
whole-level identification, rather than treating the exact maps as strictly compositional.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Topology unitInterval
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)

/-- The original exact-functor map, including its actual normalization, preserves row interchange.
-/
theorem exactOriginalPrespectrumMap_rowSwap {F : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F) (k : ℕ)
    (x : stageSpace (k + 2) (modelOf W)) :
    stageRowSwapHomeomorph k (modelOf V)
      ((exactOriginalPrespectrumMap W V hF).map (k + 3) x) =
    (exactOriginalPrespectrumMap W V hF).map (k + 3)
      (stageRowSwapHomeomorph k (modelOf W) x) :=
  stageRowSwapHomeomorph_naturality k
    (modelMap W V hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _)) x

/-- Original independent-universe transformation tracks retain the whole row-interchange square.
-/
theorem originalPrespectrumTransformationHomotopy_rowSwap {F G : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact W.cof W.weq V.cof V.weq G)
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf W)) :
    stageRowSwapHomeomorph k (modelOf V)
      ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).level
        (k + 3) (t, x)) =
    (originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).level
      (k + 3) (t, stageRowSwapHomeomorph k (modelOf W) x) :=
  stageTransformationTopHomotopy_rowSwap k
    (F := modelMap W V hF h0F) (G := modelMap W V hG h0G)
    (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (fun A => hη (AsSmall.down.obj A)) t x

/-- Canonical zero normalization preserves the entire original row-interchange track. -/
theorem exactOriginalPrespectrumHomotopy_rowSwap {F G : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact W.cof W.weq V.cof V.weq G)
    (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf W)) :
    stageRowSwapHomeomorph k (modelOf V)
      ((exactOriginalPrespectrumHomotopy W V hF hG η hη).level (k + 3) (t, x)) =
    (exactOriginalPrespectrumHomotopy W V hF hG η hη).level
      (k + 3) (t, stageRowSwapHomeomorph k (modelOf W) x) :=
  originalPrespectrumTransformationHomotopy_rowSwap W V hF.rebase hG.rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _)
    (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation_weak hF hG η hη)
    k t x

/-- The original binary normalization track commutes with row interchange at every time. -/
theorem exactOriginalPrespectrumMapCompHomotopy_rowSwap {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G) (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf W)) :
    stageRowSwapHomeomorph k (modelOf U)
      ((exactOriginalPrespectrumMapCompHomotopy W V U hF hG).level (k + 3) (t, x)) =
    (exactOriginalPrespectrumMapCompHomotopy W V U hF hG).level
      (k + 3) (t, stageRowSwapHomeomorph k (modelOf W) x) := by
  rw [exactOriginalPrespectrumMapCompHomotopy_level]
  exact originalPrespectrumTransformationHomotopy_rowSwap W U _ _ _ _ _ _ k t x

end Quillen.Waldhausen.IteratedS
