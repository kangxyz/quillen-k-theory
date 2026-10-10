/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Mathlib.CategoryTheory.Category.ULift
import Quillen.Waldhausen.Functoriality.KMap
import Quillen.Topology.HomotopyGroups.Equivalence
import Quillen.Waldhausen.Fibration.AcyclicSubcategory

/-!
# A genuine common-universe model of a Waldhausen category

`AsSmall` lifts objects and homs into their original maximum universe. Both
morphism classes are pulled back from the original category. The actual
S-constructions are simplicially isomorphic by exact up/down postcomposition.
-/
noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C]

/-- The common universe is exactly the existing realization universe. -/
abbrev SmallModel (C : Type u) [Category.{v} C] := AsSmall.{0} C

local instance smallUp_isEquivalence : (AsSmall.up : C ⥤ SmallModel C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_functor
local instance smallDown_isEquivalence : (AsSmall.down : SmallModel C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_inverse

namespace Structure
variable (W : Structure C)

/-- The chosen zero and original classes on the actual lifted small category. -/
def smallModel : Structure (SmallModel C) where
  zero := AsSmall.up.obj W.zero
  isZero := IsZero.of_full_of_faithful_of_isZero (AsSmall.down : SmallModel C ⥤ C) _ W.isZero
  cof := W.cof.inverseImage AsSmall.down
  weq := W.weq.inverseImage AsSmall.down
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.cof_iso _ (inferInstance : IsIso (AsSmall.down.map f))
  weq_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.weq_iso _ (inferInstance : IsIso (AsSmall.down.map f))
  cof_zero := by
    intro X
    change W.cof _
    convert W.cof_zero (AsSmall.down.obj X) using 1
    all_goals first | rfl | exact W.isZero.eq_of_src _ _
  pushout_exists := by
    intro A B D i f hi
    obtain ⟨P,g,j,h⟩ := W.pushout_exists (AsSmall.down.map i) (AsSmall.down.map f) hi
    exact ⟨AsSmall.up.obj P, AsSmall.up.map g, AsSmall.up.map j, h.map AsSmall.up⟩
  cof_pushout := by
    intro A B D P i f g j hi h
    exact W.cof_pushout hi (h.map AsSmall.down)
  gluing := by
    intro A B D P A' B' D' P' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact W.gluing (AsSmall.down.map a) (AsSmall.down.map b) (AsSmall.down.map d)
      (AsSmall.down.map p) hi hi' (h.map AsSmall.down) (h'.map AsSmall.down)
      (congrArg AsSmall.down.map ei) (congrArg AsSmall.down.map ef)
      (congrArg AsSmall.down.map eg) (congrArg AsSmall.down.map ej) ha hb hd

/-- Lifting preserves the original classes and all genuine pushout squares. -/
theorem smallModel_up_exact :
    IsExact W.cof W.weq W.smallModel.cof W.smallModel.weq (AsSmall.up : C ⥤ SmallModel C) where
  zero h := IsZero.of_full_of_faithful_of_isZero AsSmall.down _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map AsSmall.up

/-- Lowering forgets only the universe lifts. -/
theorem smallModel_down_exact :
    IsExact W.smallModel.cof W.smallModel.weq W.cof W.weq (AsSmall.down : SmallModel C ⥤ C) where
  zero h := IsZero.of_full_of_faithful_of_isZero (AsSmall.up : C ⥤ SmallModel C) _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map AsSmall.down

/-- The actual S-constructions lie in the same `max u v` universe and are
strictly inverse under exact up/down postcomposition. -/
def smallModelSSetIso : sSet W.cof W.weq ≅ sSet W.smallModel.cof W.smallModel.weq where
  hom := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ AsSmall.up, A.2.postcomp W.smallModel_up_exact⟩
    naturality _ _ _ := by ext A; rfl }
  inv := {
    app _ := ↾fun A ↦ ⟨A.1 ⋙ AsSmall.down, A.2.postcomp W.smallModel_down_exact⟩
    naturality _ _ _ := by ext A; rfl }
  hom_inv_id := by
    ext n A : 4
    apply Subtype.ext
    rfl
  inv_hom_id := by
    ext n A : 4
    apply Subtype.ext
    rfl

/-- This is an actual homeomorphism of the original realization spaces. -/
def smallModelDeloopingHomeomorph : W.Delooping ≃ₜ W.smallModel.Delooping :=
  TopCat.homeoOfIso (SSet.toTop.mapIso W.smallModelSSetIso)

/-- The lifted simplicial isomorphism preserves the original zero diagram exactly. -/
@[simp] theorem smallModelSSetIso_zero (n : SimplexCategoryᵒᵖ) :
    W.smallModelSSetIso.hom.app n (zeroSimplex W.cof W.weq W.zero W.isZero n) =
      zeroSimplex W.smallModel.cof W.smallModel.weq W.smallModel.zero W.smallModel.isZero n := by
  apply Subtype.ext
  rfl

/-- The actual homeomorphism retains the chosen realization basepoint. -/
@[simp] theorem smallModelDeloopingHomeomorph_basepoint :
    W.smallModelDeloopingHomeomorph W.kBasepoint = W.smallModel.kBasepoint := by
  change SSet.toTop.map W.smallModelSSetIso.hom
    (realizationPoint (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))) = _
  rw [realizationPoint_naturality, smallModelSSetIso_zero]
  rfl

/-- The original homotopy groups are identified through the actual based homeomorphism. -/
def smallModelKEquiv (n : ℕ) : W.K n ≃* W.smallModel.K n :=
  homotopyEquivPiEquiv W.smallModelDeloopingHomeomorph.toHomotopyEquiv
    W.smallModelDeloopingHomeomorph_basepoint n

@[simp] theorem smallModelKEquiv_toMonoidHom (n : ℕ) :
    (W.smallModelKEquiv n).toMonoidHom =
      piMap n W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        W.smallModelDeloopingHomeomorph_basepoint := rfl

end Structure

section Functoriality
variable {D : Type u} [Category.{v} D] {W : Structure C} {W' : Structure D}
  {F : C ⥤ D}

/-- The actual lifted functor keeps the original object and morphism map. -/
def smallModelFunctor (F : C ⥤ D) : SmallModel C ⥤ SmallModel D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- Genuine exactness survives lifting both universes. -/
theorem IsExact.smallModel (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    IsExact W.smallModel.cof W.smallModel.weq W'.smallModel.cof W'.smallModel.weq
      (smallModelFunctor F) :=
  W.smallModel_down_exact.comp (hF.comp W'.smallModel_up_exact)

/-- Original S-maps commute strictly with the actual universe-lifting isomorphisms. -/
theorem smallModelSSetIso_naturality (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    sSetMap hF ≫ W'.smallModelSSetIso.hom =
      W.smallModelSSetIso.hom ≫ sSetMap hF.smallModel := by
  ext n A : 4
  apply Subtype.ext
  rfl

/-- The square commutes as actual continuous maps, before any group transport. -/
theorem smallModelDeloopingHomeomorph_naturality
    (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    W'.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun.comp (deloopingMap hF).hom =
      (deloopingMap hF.smallModel).hom.comp W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  change (SSet.toTop.map (sSetMap hF) ≫ SSet.toTop.map W'.smallModelSSetIso.hom).hom =
    (SSet.toTop.map W.smallModelSSetIso.hom ≫ SSet.toTop.map (sSetMap hF.smallModel)).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, smallModelSSetIso_naturality]

/-- Strictly zero-preserving original functors retain their exact original K-maps. -/
theorem smallModelKEquiv_naturality_of_zeroEq
    (hF : IsExact W.cof W.weq W'.cof W'.weq F) (h0 : F.obj W.zero = W'.zero) (n : ℕ) :
    (W'.smallModelKEquiv n).toMonoidHom.comp (KMap hF n) =
      (KMap hF.smallModel n).comp (W.smallModelKEquiv n).toMonoidHom := by
  rw [Structure.smallModelKEquiv_toMonoidHom, Structure.smallModelKEquiv_toMonoidHom,
    KMap_eq_piMap_of_zeroEq hF h0,
    KMap_eq_piMap_of_zeroEq hF.smallModel (congrArg AsSmall.up.obj h0),
    ← homotopyGroupMapHom_comp, ← homotopyGroupMapHom_comp]
  congr 1
  exact smallModelDeloopingHomeomorph_naturality hF

/-- All original canonical K-maps commute with the actual small-model equivalences;
zero rebasing is transported by its genuine natural isomorphism. -/
theorem smallModelKEquiv_naturality (hF : IsExact W.cof W.weq W'.cof W'.weq F) (n : ℕ) :
    (W'.smallModelKEquiv n).toMonoidHom.comp (KMap hF n) =
      (KMap hF.smallModel n).comp (W.smallModelKEquiv n).toMonoidHom := by
  have hh := smallModelKEquiv_naturality_of_zeroEq hF.rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _) n
  have hi := (Quillen.rebaseFunctorIso F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero)).symm
  have hsmall := Functor.isoWhiskerLeft (AsSmall.down : SmallModel C ⥤ C)
    (Functor.isoWhiskerRight hi (AsSmall.up : D ⥤ SmallModel D))
  rw [KMap_eq_of_iso hF.rebase hF hi,
    KMap_eq_of_iso hF.rebase.smallModel hF.smallModel hsmall] at hh
  exact hh

end Functoriality
namespace Fibration.NestedWeakEquivalences
variable {W : Structure C} (N : NestedWeakEquivalences W)

/-- Both lifted weak models retain the same actual cofibrations and chosen zero. -/
def smallModel : NestedWeakEquivalences W.smallModel where
  coarse := N.coarse.smallModel
  cof_eq := by change N.coarse.cof.inverseImage _ = W.cof.inverseImage _; rw [N.cof_eq]
  zero_eq := congrArg AsSmall.up.obj N.zero_eq
  le_weq := fun _ _ f hf ↦ N.le_weq (AsSmall.down.map f) hf

end Fibration.NestedWeakEquivalences
end Quillen.Waldhausen
