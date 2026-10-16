/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.PushoutTransformation

/-! Actual identity, quotient order, and whole normalized endpoint squares for pushout maps. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Additivity
universe u v
namespace QuillenTest.AdditivityPushoutTransformation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure D) {F G F' G' : C ⥤ D}
  (a : F ⟶ G) (ha : ∀ X, W.cof (a.app X))

/-- Identity input squares induce the actual identity map on every original pushout. -/
theorem identity_square (f : Arrow C) :
    (pushoutTransformation W a a ha ha (𝟙 F) (𝟙 G) (by simp)).app f =
      𝟙 ((pushoutFunctor W a ha).obj f) := by
  apply (pushoutFunctor_isPushout W a ha f).hom_ext <;>
    simp [pushoutTransformation]

variable [HasBinaryCoproducts D] {H H' : C ⥤ D}
  (ηF : F ⟶ F') (ηH : H ⟶ H')

/-- The separated sum's first inclusion is the actual quotient transformation. -/
theorem quotient_first (X Y : C) :
    coprod.inl ≫ (splitEndpointTransformation ηF ηH).app (X, Y) =
      ηH.app X ≫ coprod.inl := by
  simp [splitEndpointTransformation]

variable (V : Structure C) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a') (hbη : b ≫ ηH = ηG ≫ b')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')

omit [HasBinaryCoproducts D] in
/-- The full normalized identity square retains the original middle-functor normalization. -/
theorem original_identity_family (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    Functor.whiskerLeft
        (intervalArrows (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs') ≫
        normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration n m A =
      normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration n m A ≫
        Functor.whiskerLeft A.1 (normalizedWeakTransformation hs.exactG hs'.exactG ηG) :=
  normalizedPushoutTransformation_identityEndpointFamily W a a' ηF ηG haη b b' V hs hs' n m A

include hbη in
/-- The whole separated square keeps both quotient and subobject maps in their original order. -/
theorem original_separated_family (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    Functor.whiskerLeft
        (intervalArrows (Edgewise.left n.unop n.unop) (Edgewise.right n.unop n.unop)
          (left_le_right n.unop) A.1)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs') ≫
        normalizedSeparatedEndpointFamily V W a' b' hs' n m A =
      normalizedSeparatedEndpointFamily V W a b hs n m A ≫
        Functor.whiskerLeft (separatedPairGrid A.1)
          (normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs') :=
  normalizedPushoutTransformation_separatedEndpointFamily W a a' ηF ηG haη b b' ηH hbη
    V hs hs' n m A

omit [HasBinaryCoproducts D] in
/-- The pushout zero component is exactly identity under its original zero transports. -/
theorem original_pushout_zero :
    eqToHom (normalizedPushoutFunctor_obj_zero V W a hs.exactF hs.exactG hs.cofibration).symm ≫
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app
          (Arrow.mk (𝟙 V.zero)) ≫
        eqToHom (normalizedPushoutFunctor_obj_zero V W a' hs'.exactF hs'.exactG hs'.cofibration) =
      𝟙 W.zero :=
  normalizedPushoutTransformation_zero W a a' ηF ηG haη b b' V hs hs'

/-- The separated pair-of-zeros uses the actual quotient-first normalized component. -/
theorem original_split_zero :
    eqToHom (normalizedSplitEndpoint_obj_zero V W hs.exactH hs.exactF).symm ≫
        (normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs').app
          (V.zero, V.zero) ≫
        eqToHom (normalizedSplitEndpoint_obj_zero V W hs'.exactH hs'.exactF) =
      𝟙 W.zero :=
  normalizedSplitEndpointTransformation_zero W a a' ηF b b' ηH V hs hs'

end QuillenTest.AdditivityPushoutTransformation
