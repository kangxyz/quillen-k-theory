import Quillen.Waldhausen.ExtensionCategory.SplitQuotient
import Quillen.Waldhausen.Additivity.RealizedAdditivity
import Quillen.Waldhausen.SConstruction.WeakNaturalTransformation

/-! # Genuine extension-category additivity on realization

The actual source/cofiber functor realizes to a homotopy equivalence from
extensions to the S-construction of the actual product category. The proof
uses the internal structural cofibration sequence and functor additivity.

This realization statement uses the honest common-universe case: both the
objects and morphisms of the original category lie in universe `u`. It does
not identify realization of a product with a product of realizations and
makes no based-homotopy assertion.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory

section MapLaws
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (V : Structure C) (W : Structure D) (U : Structure E)

/-- Strict identity for the original S-construction map. -/
theorem sSetMap_identity : sSetMap (IsExact.id V.cof V.weq) = 𝟙 (sSet V.cof V.weq) := by
  ext n A
  rfl

/-- Strict composition for the original S-construction map. -/
theorem sSetMap_composition {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact W.cof W.weq U.cof U.weq G) :
    sSetMap (hF.comp hG) = sSetMap hF ≫ sSetMap hG := by
  ext n A
  rfl

/-- Strict identity on the original realization. -/
theorem deloopingMap_identity : (deloopingMap (IsExact.id V.cof V.weq)).hom =
    ContinuousMap.id V.Delooping := by
  unfold deloopingMap
  rw [sSetMap_identity, CategoryTheory.Functor.map_id]
  rfl

/-- Strict composition on the original realization. -/
theorem deloopingMap_composition {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact W.cof W.weq U.cof U.weq G) :
    (deloopingMap (hF.comp hG)).hom = (deloopingMap hG).hom.comp (deloopingMap hF).hom := by
  unfold deloopingMap
  rw [sSetMap_composition V W U, CategoryTheory.Functor.map_comp]
  rfl

/-- Actual natural isomorphisms give homotopies of the original exact-functor maps. -/
theorem deloopingMap_homotopic_of_iso {F G : C ⥤ D}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (e : F ≅ G) :
    (deloopingMap hF).hom.Homotopic (deloopingMap hG).hom :=
  ⟨weakNaturalTransformationRealizationHomotopy V W hF hG e.hom
    (fun X ↦ W.weq_iso (e.hom.app X) inferInstance)⟩
end MapLaws

variable {C : Type u} [Category.{u} C] (W : Structure C)

section ChosenCoproducts
variable [HasBinaryCoproducts C] [HasBinaryCoproducts (Obj W)]

/-- The actual split/source-cofiber composite is homotopic to the identity
on extensions, by the genuine internal structural sequence. -/
theorem sourceCofiber_split_homotopic :
    ((deloopingMap (split_exact W)).hom.comp
      (deloopingMap (sourceCofiber_exact W)).hom).Homotopic
        (ContinuousMap.id (waldhausenStructure W).Delooping) := by
  let V := waldhausenStructure W
  have hs := internalIsCofibrationSequence W
  have ha := Additivity.deloopingMap_additivity V V
    (identityToExtension W) (extensionToZero W) hs
  have hi := deloopingMap_homotopic_of_iso V V
    (Additivity.sumFunctor_isExact V V hs.exactH hs.exactF)
    ((sourceCofiber_exact W).comp (split_exact W)) (internalSumSplitIso W)
  have h := (ha.trans hi).symm
  rw [deloopingMap_composition V (productStructure W W) V,
    deloopingMap_identity V] at h
  exact h

/-- The reverse composite is homotopic to the identity by the actual
natural identification of split cofibers. -/
theorem split_sourceCofiber_homotopic :
    ((deloopingMap (sourceCofiber_exact W)).hom.comp
      (deloopingMap (split_exact W)).hom).Homotopic
        (ContinuousMap.id (productStructure W W).Delooping) := by
  have h := deloopingMap_homotopic_of_iso (productStructure W W) (productStructure W W)
    ((split_exact W).comp (sourceCofiber_exact W))
    (IsExact.id (productStructure W W).cof (productStructure W W).weq)
    (splitSourceCofiberIso W)
  rw [deloopingMap_composition (productStructure W W) (waldhausenStructure W)
    (productStructure W W), deloopingMap_identity] at h
  exact h

end ChosenCoproducts

/-- The actual split map, using coproducts supplied by the Waldhausen axioms. -/
def splitRealizationMap : C((productStructure W W).Delooping, (waldhausenStructure W).Delooping) := by
  letI := Additivity.hasBinaryCoproducts W
  letI := Additivity.hasBinaryCoproducts (waldhausenStructure W)
  exact (deloopingMap (split_exact W)).hom

/-- Genuine extension-category additivity. Its forward map is exactly the
realized source/cofiber map into the actual product-category S-construction. -/
def realizationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (waldhausenStructure W).Delooping (productStructure W W).Delooping := by
  letI := Additivity.hasBinaryCoproducts W
  letI := Additivity.hasBinaryCoproducts (waldhausenStructure W)
  exact {
    toFun := (deloopingMap (sourceCofiber_exact W)).hom
    invFun := (deloopingMap (split_exact W)).hom
    left_inv := sourceCofiber_split_homotopic W
    right_inv := split_sourceCofiber_homotopic W }

@[simp] theorem realizationHomotopyEquiv_toFun :
    (realizationHomotopyEquiv W).toFun = (deloopingMap (sourceCofiber_exact W)).hom := rfl

@[simp] theorem realizationHomotopyEquiv_invFun :
    (realizationHomotopyEquiv W).invFun = splitRealizationMap W := rfl

end Quillen.Waldhausen.ExtensionCategory
