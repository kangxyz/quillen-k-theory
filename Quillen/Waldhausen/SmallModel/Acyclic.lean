/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.SmallModel.Basic
import Quillen.Waldhausen.Fibration.CanonicalFiberMap

/-! # Original acyclic categories and extension data under the common-universe lift -/
noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C]
local instance : (AsSmall.up : C ⥤ SmallModel C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_functor
local instance : (AsSmall.down : SmallModel C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_inverse

namespace Structure
variable (W : Structure C)

/-- The lifted weak class retains the original two-out-of-three property. -/
instance smallModel_twoOutOfThree [W.weq.HasTwoOutOfThreeProperty] :
    W.smallModel.weq.HasTwoOutOfThreeProperty := inferInstanceAs
  ((W.weq.inverseImage (AsSmall.down : SmallModel C ⥤ C)).HasTwoOutOfThreeProperty)

/-- The actual zero-to-object morphism lowers to the original zero-to-object morphism. -/
@[simp] theorem smallModel_zero_to (X : SmallModel C) :
    AsSmall.down.map (W.smallModel.isZero.to_ X) = W.isZero.to_ (AsSmall.down.obj X) :=
  W.isZero.eq_of_src _ _

/-- The actual object-to-zero morphism is likewise unchanged after lowering. -/
@[simp] theorem smallModel_from_zero (X : SmallModel C) :
    AsSmall.down.map (W.smallModel.isZero.from_ X) = W.isZero.from_ (AsSmall.down.obj X) :=
  W.isZero.eq_of_tgt _ _

/-- Extension is inherited on the original cofiber diagrams after lowering. -/
theorem smallModel_extensionAxiom (he : Fibration.ExtensionAxiom W) :
    Fibration.ExtensionAxiom W.smallModel where
  extension hi hi' h h' a b c wi wq ha hc := by
    have hp := h.map (AsSmall.down : SmallModel C ⥤ C)
    have hp' := h'.map (AsSmall.down : SmallModel C ⥤ C)
    simp only [smallModel_zero_to, smallModel_from_zero] at hp hp'
    exact he.extension hi hi' hp hp' (AsSmall.down.map a) (AsSmall.down.map b)
      (AsSmall.down.map c) (congrArg AsSmall.down.map wi) (congrArg AsSmall.down.map wq) ha hc

/-- Lifted coarse acyclicity is the original actual predicate. -/
@[simp] theorem smallModel_acyclic_iff (X : SmallModel C) :
    Fibration.Acyclic W.smallModel X ↔ Fibration.Acyclic W (AsSmall.down.obj X) := by
  change W.weq (AsSmall.down.map (W.smallModel.isZero.to_ X)) ↔ _
  rw [smallModel_zero_to]
  rfl

end Structure
namespace Fibration
variable {W : Structure C} (N : NestedWeakEquivalences W)

/-- The original acyclic object, with only its objects and morphisms lifted. -/
def acyclicSmallUp : AcyclicCategory N ⥤ AcyclicCategory N.smallModel where
  obj X := ⟨AsSmall.up.obj X.obj, (N.coarse.smallModel_acyclic_iff _).2 X.property⟩
  map f := (acyclicObjects N.smallModel).homMk (AsSmall.up.map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Lowering retains precisely the original coarse-acyclic witness. -/
def acyclicSmallDown : AcyclicCategory N.smallModel ⥤ AcyclicCategory N where
  obj X := ⟨AsSmall.down.obj X.obj, (N.coarse.smallModel_acyclic_iff _).1 X.property⟩
  map f := (acyclicObjects N).homMk (AsSmall.down.map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both functors are inverse on the original objects and arrows. -/
def acyclicSmallEquivalence : AcyclicCategory N ≌ AcyclicCategory N.smallModel where
  functor := acyclicSmallUp N
  inverse := acyclicSmallDown N
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

local instance : (acyclicSmallUp N).IsEquivalence := (acyclicSmallEquivalence N).isEquivalence_functor
local instance : (acyclicSmallDown N).IsEquivalence := (acyclicSmallEquivalence N).isEquivalence_inverse

/-- The forward equivalence retains genuine fine cofibrations and weaknesses. -/
theorem acyclicSmallUp_exact : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    (acyclicStructure N.smallModel).cof (acyclicStructure N.smallModel).weq (acyclicSmallUp N) where
  zero h := IsZero.of_full_of_faithful_of_isZero (acyclicSmallDown N) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (acyclicSmallUp N)

/-- The inverse equivalence retains the same actual fine structure. -/
theorem acyclicSmallDown_exact : IsExact
    (acyclicStructure N.smallModel).cof (acyclicStructure N.smallModel).weq
    (acyclicStructure N).cof (acyclicStructure N).weq (acyclicSmallDown N) where
  zero h := IsZero.of_full_of_faithful_of_isZero (acyclicSmallUp N) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (acyclicSmallDown N)

/-- The actual acyclic S-constructions are isomorphic in their original maximum universe. -/
def acyclicSmallSSetIso :
    sSet (acyclicStructure N).cof (acyclicStructure N).weq ≅
      sSet (acyclicStructure N.smallModel).cof (acyclicStructure N.smallModel).weq where
  hom := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ acyclicSmallUp N, A.2.postcomp (acyclicSmallUp_exact N)⟩
    naturality _ _ _ := by ext A; rfl }
  inv := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ acyclicSmallDown N, A.2.postcomp (acyclicSmallDown_exact N)⟩
    naturality _ _ _ := by ext A; rfl }
  hom_inv_id := by ext n A : 4; apply Subtype.ext; rfl
  inv_hom_id := by ext n A : 4; apply Subtype.ext; rfl

/-- The lifted coarse/fine map is the original map in the actual lifted coordinates. -/
theorem smallModelSSetIso_changeWeak :
    sSetMap (changeWeak_exact N) ≫ N.coarse.smallModelSSetIso.hom =
      W.smallModelSSetIso.hom ≫ sSetMap (changeWeak_exact N.smallModel) := by
  ext n A : 4
  apply Subtype.ext
  rfl

/-- Original acyclic inclusions commute with the precise lifted S-construction maps. -/
theorem acyclicSmallSSetIso_inclusion :
    sSetMap (acyclicInclusion_exact N) ≫ W.smallModelSSetIso.hom =
      (acyclicSmallSSetIso N).hom ≫ sSetMap (acyclicInclusion_exact N.smallModel) := by
  ext n A : 4
  apply Subtype.ext
  rfl

/-- The same equation holds for the original coarse inclusion. -/
theorem acyclicSmallSSetIso_coarseInclusion :
    sSetMap (acyclicInclusion_coarse_exact N) ≫ N.coarse.smallModelSSetIso.hom =
      (acyclicSmallSSetIso N).hom ≫ sSetMap (acyclicInclusion_coarse_exact N.smallModel) := by
  ext n A : 4
  apply Subtype.ext
  rfl

/-- The inherited original acyclic zero is retained by the lifted simplicial map. -/
@[simp] theorem acyclicSmallSSetIso_zero (n : SimplexCategoryᵒᵖ) :
    (acyclicSmallSSetIso N).hom.app n
      (zeroSimplex (acyclicStructure N).cof (acyclicStructure N).weq
        (acyclicStructure N).zero (acyclicStructure N).isZero n) =
      zeroSimplex (acyclicStructure N.smallModel).cof (acyclicStructure N.smallModel).weq
        (acyclicStructure N.smallModel).zero (acyclicStructure N.smallModel).isZero n := by
  apply Subtype.ext
  rfl

/-- The actual lifted acyclic realization homeomorphism. -/
def acyclicSmallDeloopingHomeomorph : (acyclicStructure N).Delooping ≃ₜ
    (acyclicStructure N.smallModel).Delooping :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (acyclicSmallSSetIso N))

@[simp] theorem acyclicSmallDeloopingHomeomorph_basepoint :
    acyclicSmallDeloopingHomeomorph N (acyclicStructure N).kBasepoint =
      (acyclicStructure N.smallModel).kBasepoint := by
  change SSet.toTop.map (acyclicSmallSSetIso N).hom
    (realizationPoint (zeroSimplex _ _ _ _ (op ⦋0⦌))) = _
  rw [realizationPoint_naturality, acyclicSmallSSetIso_zero]
  rfl

end Fibration
end Quillen.Waldhausen
