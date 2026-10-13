/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.ExtensionCategory.Embeddings

/-! # The internal identity/subextension/quotient sequence

The sequence `(A→A) → (A→B) → (0→B/A)` consists of actual exact endofunctors
of the genuine extension Waldhausen category. Its relative condition is
proved by the original relative pushout map, not postulated.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Pointwise, the identity-source subextension is a genuine Reedy cofibration. -/
theorem identityToExtension_cof (X : Obj W) : cof W ((identityToExtension W).app X) :=
  cof_of_relative W _ (W.cof.id_mem _) (IsPushout.of_id_fst (f := 𝟙 X.obj.left))
    X.obj.hom (by
      simp only [identityToExtension, Functor.comp_obj, Functor.id_obj]
      exact Category.id_comp X.obj.hom) (by simp) X.property

/-- The displayed pushout extension is `A' → B ⨿[A] A'`. -/
def subextensionPushout {X Y : Obj W} (f : X ⟶ Y) : Obj W :=
  ⟨Arrow.mk (Additivity.targetι W (inclusion W) (inclusion_cof W) (Arrow.mk f)),
    Additivity.targetι_cof W (inclusion W) (inclusion_cof W) (Arrow.mk f)⟩

/-- The map from `X` to the pushout attaching the identity extension on the source of `Y` along
`f`, using `f` on sources and the pushout inclusion on targets. -/
def subextensionInl {X Y : Obj W} (f : X ⟶ Y) : X ⟶ subextensionPushout W f :=
  (objects W).homMk (Arrow.homMk f.hom.left
    (Additivity.sourceι W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)).w.symm)

/-- The map from the identity extension on the source of `Y` into `subextensionPushout W f`,
using the identity on sources and the other pushout inclusion on targets. -/
def subextensionInr {X Y : Obj W} (f : X ⟶ Y) :
    (source W ⋙ identityEmbedding W).obj Y ⟶ subextensionPushout W f :=
  (objects W).homMk (Arrow.homMk (𝟙 _)
    (Additivity.targetι W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (by simp [subextensionPushout, identityEmbedding, source]))

/-- The comparison from the subextension pushout to `Y`, using the identity on sources and
`relativeMap W f` on targets. -/
def subextensionComparison {X Y : Obj W} (f : X ⟶ Y) : subextensionPushout W f ⟶ Y :=
  (objects W).homMk (Arrow.homMk (𝟙 _) (relativeMap W f) (by
    simpa only [Category.id_comp] using!
      (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)).symm))

/-- Both component squares, and hence the extension square, are actual pushouts. -/
theorem subextension_isPushout {X Y : Obj W} (f : X ⟶ Y) :
    IsPushout ((identityToExtension W).app X) ((source W ⋙ identityEmbedding W).map f)
      (subextensionInl W f) (subextensionInr W f) :=
  IsPushout.of_map_of_faithful (forget W) (arrow_isPushout _ _ _ _ IsPushout.of_id_fst
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f)))

@[reassoc (attr := simp)] theorem subextensionInl_comparison {X Y : Obj W} (f : X ⟶ Y) :
    subextensionInl W f ≫ subextensionComparison W f = f := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · simp [subextensionInl, subextensionComparison]
  · exact Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)

@[reassoc (attr := simp)] theorem subextensionInr_comparison {X Y : Obj W} (f : X ⟶ Y) :
    subextensionInr W f ≫ subextensionComparison W f = (identityToExtension W).app Y := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · simp [subextensionInr, subextensionComparison, identityToExtension, identityEmbedding,
    source, forget]
  · exact Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f)

/-- The new relative comparison is Reedy cofibrant precisely by the original
relative target cofibration, with identity source component. -/
theorem subextensionComparison_cof {X Y : Obj W} (f : X ⟶ Y) (hf : cof W f) :
    cof W (subextensionComparison W f) :=
  cof_of_relative W _ (W.cof.id_mem _)
    (IsPushout.of_id_snd (f := (subextensionPushout W f).obj.hom)) (relativeMap W f)
    (by simp [subextensionComparison]) (Additivity.targetι_comparison W (inclusion W)
      (inclusion_cof W) (Arrow.mk f)) hf.2

private theorem comparison_cof_of_displayed
    {D : Type*} [Category* D] (V : Structure D) {F G : Obj W ⥤ D}
    (a : F ⟶ G) (ha : ∀ X, V.cof (a.app X)) {X Y : Obj W} (f : X ⟶ Y)
    {P : D} {i : G.obj X ⟶ P} {j : F.obj Y ⟶ P}
    (h : IsPushout (a.app X) (F.map f) i j) (k : P ⟶ G.obj Y)
    (hi : i ≫ k = G.map f) (hj : j ≫ k = a.app Y) (hk : V.cof k) :
    V.cof (Additivity.comparison V a ha (Arrow.mk f)) := by
  let h₀ := Additivity.pushoutFunctor_isPushout V a ha (Arrow.mk f)
  let e := h₀.isoIsPushout _ _ h
  have he : e.hom ≫ k = Additivity.comparison V a ha (Arrow.mk f) := by
    apply h₀.hom_ext
    · rw [← Category.assoc, h₀.inl_isoIsPushout_hom, hi]
      exact (Additivity.sourceι_comparison V a ha (Arrow.mk f)).symm
    · rw [← Category.assoc, h₀.inr_isoIsPushout_hom, hj]
      exact (Additivity.targetι_comparison V a ha (Arrow.mk f)).symm
  rw [← he]
  exact V.cof.comp_mem _ _ (V.cof_iso _ (inferInstance : IsIso e.hom)) hk

/-- The internal subextension transformation satisfies the genuine relative condition. -/
theorem identityToExtension_isCofibrationTransformation :
    Additivity.IsCofibrationTransformation (waldhausenStructure W)
      (identityToExtension W) (waldhausenStructure W) where
  app_cof := identityToExtension_cof W
  relative_cof f hf := comparison_cof_of_displayed W (waldhausenStructure W)
    (identityToExtension W) (identityToExtension_cof W) f (subextension_isPushout W f)
    (subextensionComparison W f) (subextensionInl_comparison W f) (subextensionInr_comparison W f)
    (subextensionComparison_cof W f hf)

/-- The quotient square of the internal extension sequence is a genuine pushout. -/
theorem internal_cofiber_isPushout (X : Obj W) :
    IsPushout ((identityToExtension W).app X)
      ((isZero W).from_ ((source W ⋙ identityEmbedding W).obj X))
      ((extensionToZero W).app X)
      ((isZero W).to_ ((cofiber W ⋙ zeroEmbedding W).obj X)) := by
  apply IsPushout.of_map_of_faithful (forget W)
  apply arrow_isPushout
  · have h₀ : ((isZero W).from_ ((source W ⋙ identityEmbedding W).obj X)).hom.left =
        W.isZero.from_ X.obj.left := W.isZero.eq_of_tgt _ _
    have h₁ : ((isZero W).to_ ((cofiber W ⋙ zeroEmbedding W).obj X)).hom.left =
        𝟙 W.zero := W.isZero.eq_of_src _ _
    change IsPushout (𝟙 X.obj.left)
      (((isZero W).from_ ((source W ⋙ identityEmbedding W).obj X)).hom.left)
      (W.isZero.from_ X.obj.left)
      (((isZero W).to_ ((cofiber W ⋙ zeroEmbedding W).obj X)).hom.left)
    rw [h₀, h₁]
    exact IsPushout.of_id_fst
  · have h₀ : ((isZero W).from_ ((source W ⋙ identityEmbedding W).obj X)).hom.right =
        W.isZero.from_ X.obj.left := W.isZero.eq_of_tgt _ _
    have h₁ : ((isZero W).to_ ((cofiber W ⋙ zeroEmbedding W).obj X)).hom.right =
        W.isZero.to_ ((cofiber W).obj X) := W.isZero.eq_of_src _ _
    change IsPushout X.obj.hom
      (((isZero W).from_ ((source W ⋙ identityEmbedding W).obj X)).hom.right)
      ((quotient W).app X)
      (((isZero W).to_ ((cofiber W ⋙ zeroEmbedding W).obj X)).hom.right)
    rw [h₀, h₁]
    exact cofiber_isPushout W X

/-- The actual internal sequence of exact extension-category endofunctors. -/
theorem internalIsCofibrationSequence :
    Additivity.IsCofibrationSequence (waldhausenStructure W) (waldhausenStructure W)
      (identityToExtension W) (extensionToZero W) where
  exactF := (source_exact W).comp (identityEmbedding_exact W)
  exactG := IsExact.id _ _
  exactH := (cofiber_exact W).comp (zeroEmbedding_exact W)
  cofibration := identityToExtension_isCofibrationTransformation W
  cofiber := internal_cofiber_isPushout W

end Quillen.Waldhausen.ExtensionCategory
