/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.PointedFunctor
public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationBased
public import Quillen.Topology.Realization.Constant

/-! # Functoriality and weak-transformation invariance of the original K-maps

The original canonical zero rebasing is retained throughout. Every homotopy
used below is the actual nerve-direction homotopy of a pointwise weak natural
transformation, with its chosen-zero track proved constant.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable {V : Structure C} {W : Structure D} {U : Structure E}
variable {F G : C ⥤ D}

/-- A strict chosen-zero equality makes the original realization map based. -/
theorem deloopingMap_basepoint_of_zeroEq
    (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero) :
    deloopingMap hF V.kBasepoint = W.kBasepoint := by
  have h := deloopingMap_basepoint hF V.zero V.isZero
  simpa only [h0] using h

/-- The original canonical rebasing preserves the specified realization points. -/
theorem KMap_basepoint (hF : IsExact V.cof V.weq W.cof W.weq F) :
    deloopingMap hF.rebase V.kBasepoint = W.kBasepoint :=
  deloopingMap_basepoint_of_zeroEq hF.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _)

private theorem groupsMapOfZeroEq_eq_piMap
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z') (h0 : F.obj Z = Z') (n : ℕ)
    (hb : deloopingMap hF (basepoint V.cof V.weq Z hZ) = basepoint W.cof W.weq Z' hZ') :
    groupsMapOfZeroEq hF Z hZ Z' hZ' h0 n = Quillen.piMap n (deloopingMap hF).hom hb := by
  subst Z'
  rfl

/-- The public K-map is exactly the based map of its original canonical rebasing. -/
theorem KMap_eq_piMap (hF : IsExact V.cof V.weq W.cof W.weq F) (n : ℕ) :
    KMap hF n = Quillen.piMap n (deloopingMap hF.rebase).hom (KMap_basepoint hF) :=
  groupsMapOfZeroEq_eq_piMap hF.rebase V.zero V.isZero W.zero W.isZero
    (Quillen.rebaseFunctor_obj_base _ _ _ _) n (KMap_basepoint hF)

/-- Conjugate the actual transformation by the two canonical zero normalizations. -/
def normalizedWeakTransformation
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G) :
    Quillen.rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero) ⟶
      Quillen.rebaseFunctor G V.zero W.zero ((hG.zero V.isZero).iso W.isZero) :=
  (Quillen.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)).inv ≫ η ≫
    (Quillen.rebaseFunctorIso G V.zero W.zero ((hG.zero V.isZero).iso W.isZero)).hom

/-- Actual pointwise weakness survives this concrete conjugation. -/
theorem normalizedWeakTransformation_weak
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G)
    (hη : ∀ X, W.weq (η.app X)) (X : C) :
    W.weq ((normalizedWeakTransformation hF hG η).app X) :=
  W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _ (hη X) (W.weq_iso _ inferInstance))

/-- A pointwise weak natural transformation gives equality of the original
canonical chosen-zero K-homomorphisms in every degree. -/
theorem KMap_eq_of_weakNatTrans
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G)
    (hη : ∀ X, W.weq (η.app X)) (n : ℕ) : KMap hF n = KMap hG n := by
  rw [KMap_eq_piMap hF n, KMap_eq_piMap hG n]
  exact Quillen.piMap_eq_of_based_homotopy n _ _
    (weakNaturalTransformationRealizationHomotopy V W hF.rebase hG.rebase
      (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation_weak hF hG η hη))
    (weakNaturalTransformationRealizationHomotopy_fixed_zero V W hF.rebase hG.rebase
      (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation_weak hF hG η hη)
      (Quillen.rebaseFunctor_obj_base _ _ _ _) (Quillen.rebaseFunctor_obj_base _ _ _ _))

/-- Natural isomorphisms preserve the original canonical K-map. -/
theorem KMap_eq_of_iso
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (e : F ≅ G) (n : ℕ) :
    KMap hF n = KMap hG n :=
  KMap_eq_of_weakNatTrans hF hG e.hom (fun _ ↦ W.weq_iso _ inferInstance) n

/-- If the original functor is already strictly based, its public K-map is
exactly the based map of the original, unmodified realization map. -/
theorem KMap_eq_piMap_of_zeroEq
    (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero) (n : ℕ) :
    KMap hF n = Quillen.piMap n (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0) := by
  rw [KMap_eq_piMap hF n]
  let η := (Quillen.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)).inv
  exact Quillen.piMap_eq_of_based_homotopy n _ _
    (weakNaturalTransformationRealizationHomotopy V W hF.rebase hF η
      (fun _ ↦ W.weq_iso _ inferInstance))
    (weakNaturalTransformationRealizationHomotopy_fixed_zero V W hF.rebase hF η
      (fun _ ↦ W.weq_iso _ inferInstance) (Quillen.rebaseFunctor_obj_base _ _ _ _) h0)

/-- The original S-map preserves composition exactly. -/
@[simp] theorem sSetMap_comp_sSetMap {J : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hJ : IsExact W.cof W.weq U.cof U.weq J) :
    sSetMap hF ≫ sSetMap hJ =
      sSetMap (hF.comp hJ) := by
  ext n A
  rfl


/-- Identity is retained by the original realization map. -/
@[simp] theorem deloopingMap_id (V : Structure C) :
    deloopingMap (IsExact.id V.cof V.weq) = 𝟙 V.Delooping := by
  rw [deloopingMap, sSetMap_id]
  exact SSet.toTop.map_id _

/-- Composition is retained by the original realization map. -/
@[simp] theorem deloopingMap_comp_deloopingMap {J : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hJ : IsExact W.cof W.weq U.cof U.weq J) :
    deloopingMap hF ≫ deloopingMap hJ =
      deloopingMap (hF.comp hJ) := by
  simp only [deloopingMap, ← Functor.map_comp, sSetMap_comp_sSetMap]


private theorem piMap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (h : f = g) : Quillen.piMap n f hf = Quillen.piMap n g hg := by
  subst g
  rfl

/-- Identity exact functors give the identity on the original K-groups. -/
@[simp] theorem KMap_id (V : Structure C) (n : ℕ) :
    KMap (IsExact.id V.cof V.weq) n = MonoidHom.id (V.K n) := by
  rw [KMap_eq_piMap_of_zeroEq (IsExact.id V.cof V.weq) rfl n]
  have he : (deloopingMap (IsExact.id V.cof V.weq)).hom = ContinuousMap.id _ :=
    congrArg TopCat.Hom.hom (deloopingMap_id V)
  exact (piMap_congr n _ rfl he).trans Quillen.homotopyGroupMapHom_id

/-- Composition of exact functors gives composition of the original canonical
chosen-zero K-homomorphisms. -/
@[simp] theorem KMap_comp_KMap {J : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hJ : IsExact W.cof W.weq U.cof U.weq J) (n : ℕ) :
    (KMap hJ n).comp (KMap hF n) =
      KMap (hF.comp hJ) n := by
  symm
  let eF := Quillen.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
  let eJ := Quillen.rebaseFunctorIso J W.zero U.zero ((hJ.zero W.isZero).iso U.isZero)
  have h0 : ((Quillen.rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)) ⋙
      (Quillen.rebaseFunctor J W.zero U.zero ((hJ.zero W.isZero).iso U.isZero))).obj V.zero =
          U.zero := by
    change (Quillen.rebaseFunctor J W.zero U.zero ((hJ.zero W.isZero).iso U.isZero)).obj
      ((Quillen.rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)).obj V.zero) =
          U.zero
    rw [Quillen.rebaseFunctor_obj_base, Quillen.rebaseFunctor_obj_base]
  have he := KMap_eq_of_iso (hF.comp hJ) (hF.rebase.comp hJ.rebase)
    (Functor.isoWhiskerRight eF J ≪≫ Functor.isoWhiskerLeft _ eJ) n
  rw [he, KMap_eq_piMap_of_zeroEq _ h0 n, KMap_eq_piMap hF n, KMap_eq_piMap hJ n]
  exact (piMap_congr n
    (f := (deloopingMap (hF.rebase.comp hJ.rebase)).hom)
    (g := (deloopingMap hJ.rebase).hom.comp (deloopingMap hF.rebase).hom) _
    ((congrArg (deloopingMap hJ.rebase).hom (KMap_basepoint hF)).trans (KMap_basepoint hJ))
    (congrArg TopCat.Hom.hom ((deloopingMap_comp_deloopingMap hF.rebase hJ.rebase).symm))).trans
      (Quillen.homotopyGroupMapHom_comp (N := Fin (n + 1))
        (deloopingMap hF.rebase).hom (KMap_basepoint hF)
        (deloopingMap hJ.rebase).hom (KMap_basepoint hJ))


/-- The actual constant functor at the specified target zero. -/
def zeroFunctor (W : Structure D) : C ⥤ D :=
  (Functor.const C).obj W.zero

/-- The actual chosen-zero functor is exact for every Waldhausen structure. -/
theorem zeroFunctor_isExact (V : Structure C) (W : Structure D) :
    IsExact V.cof V.weq W.cof W.weq (zeroFunctor (C := C) W) where
  zero _ := W.isZero
  cofibration _ _ := W.cof.id_mem W.zero
  weak _ _ := W.weq.id_mem W.zero
  pushout _ _ := IsPushout.id_horiz (𝟙 W.zero)

/-- Its original simplicial map is exactly the constant chosen-zero map. -/
theorem sSetMap_zeroFunctor (V : Structure C) (W : Structure D) :
    sSetMap (zeroFunctor_isExact V W) =
      SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n A
  apply Subtype.ext
  rfl

/-- Its original realization map is exactly the constant chosen-zero map. -/
theorem deloopingMap_zeroFunctor (V : Structure C) (W : Structure D) :
    (deloopingMap (zeroFunctor_isExact V W)).hom =
      ContinuousMap.const V.Delooping W.kBasepoint := by
  ext p
  change SSet.toTop.map (sSetMap (zeroFunctor_isExact V W)) p = W.kBasepoint
  rw [sSetMap_zeroFunctor]
  exact Quillen.realization_const_apply _ p

/-- The actual zero functor gives the trivial original K-homomorphism. -/
@[simp] theorem KMap_zeroFunctor (V : Structure C) (W : Structure D) (n : ℕ) :
    KMap (zeroFunctor_isExact V W) n = 1 := by
  rw [KMap_eq_piMap_of_zeroEq (zeroFunctor_isExact V W) rfl n]
  exact (piMap_congr n _ rfl (deloopingMap_zeroFunctor V W)).trans (Quillen.piMap_const n)

end Quillen.Waldhausen
