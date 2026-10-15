/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.GrothendieckComparison.Edges
public import Quillen.KTheory.Map.CoherenceData
public import Quillen.KTheory.GrothendieckGroup.Map

/-!
# Naturality of the canonical K₀ comparison

This file compares the actual based-loop map with the Q-arrow object classes;
all basepoint transports use the canonical zero-object isomorphism already
used by `CategoryTheory.ExactCategory.ExactFunctor.KMap`.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Topology ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen

/-- The actual π₁/fundamental-group isomorphism respects based continuous maps. -/
lemma pi1MulEquivFundamentalGroup_naturality
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (homotopyGroupMap f h a) =
      FundamentalGroup.mapOfEq f h (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    rw [FundamentalGroup.mapOfEq_apply]
    change (⟦genLoopEquivOfUnique (Fin 1) (genLoopPostcomp f h p)⟧ :
      FundamentalGroup Y y) =
      ⟦((genLoopEquivOfUnique (Fin 1) p).map f.continuous).cast h.symm h.symm⟧
    congr 1

/-- Realizing a functor maps an arrow path to its image arrow path, with
both endpoints transported by the exact vertex equalities. -/
lemma classifyingSpacePath_map {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    ((classifyingSpacePath f).map (classifyingSpaceMap F).hom.continuous).cast
      (classifyingSpaceMap_point F x).symm (classifyingSpaceMap_point F y).symm =
      classifyingSpacePath (F.map f) := by
  ext t
  exact classifyingSpacePath_naturality F f t

/-- The canonical category-to-fundamental-groupoid functor is natural up to
the exact equality between mapped object vertices. -/
def classifyingFundamentalGroupoidNaturality
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    classifyingFundamentalGroupoidFunctor C ⋙ FundamentalGroupoid.map (classifyingSpaceMap F).hom ≅
      F ⋙ classifyingFundamentalGroupoidFunctor D :=
  NatIso.ofComponents (fun x => eqToIso (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMap_point F x))) (by
    intro x y f
    apply (cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMap_point F x).symm))).1
    simp only [eqToIso, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [Category.assoc]
    change eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMap_point F x).symm) ≫
      (⟦(classifyingSpacePath f).map (classifyingSpaceMap F).hom.continuous⟧ :
        Path.Homotopic.Quotient _ _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMap_point F y)) = _
    rw [FundamentalGroupoid.conj_eqToHom
      (classifyingSpaceMap_point F x).symm (classifyingSpaceMap_point F y).symm]
    exact congrArg Path.Homotopic.Quotient.mk (classifyingSpacePath_map F f))

end Quillen

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : ExactStructure C)

/-- The object-loop construction commutes with functors between groupoids. -/
lemma qObjectClass_comp {D T : Type*} [Groupoid D] [Groupoid T]
    (F : E.QCategory ⥤ D) (G : D ⥤ T) (X : C) :
    E.qObjectClass (F ⋙ G) X = G.map (E.qObjectClass F X) := by
  simp [qObjectClass]

/-- Naturally isomorphic Q-groupoid functors give conjugate object-loop classes. -/
lemma qObjectClass_natIso {D : Type*} [Groupoid D]
    {F G : E.QCategory ⥤ D} (η : F ≅ G) (X : C) :
    E.qObjectClass G X = (η.app E.qZero).conj (E.qObjectClass F X) := by
  simp only [qObjectClass, Iso.conj_apply, Iso.app_hom, Iso.app_inv]
  apply (cancel_mono (G.map (E.fromZero (Q.of E.deflation E.inflation X)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← η.hom.naturality (E.fromZero (Q.of E.deflation E.inflation X))]
  simp only [IsIso.inv_hom_id_assoc]
  exact (NatIso.naturality_1 η (E.fromZeroTotal (Q.of E.deflation E.inflation X))).symm

/-- Realization sends the canonical object-loop class through the functor
on Q, with precisely the chosen equality of target basepoints. -/
lemma fundamentalMap_qObjectClass {D : Type u} [Category.{max u v} D]
    (F : E.QCategory ⥤ D) (d : D) (h : F.obj E.qZero = d) (X : C) :
    FundamentalGroup.mapOfEq (X := ClassifyingSpace E.QCategory) (Y := ClassifyingSpace D)
        (x := classifyingSpacePoint E.qZero) (y := classifyingSpacePoint d) (classifyingSpaceMap
          F).hom
        ((classifyingSpaceMap_point F E.qZero).trans (congrArg classifyingSpacePoint h))
        (E.qObjectClass (classifyingFundamentalGroupoidFunctor E.QCategory) X) =
      ((classifyingFundamentalGroupoidFunctor D).mapIso (eqToIso h)).conj
        (E.qObjectClass (F ⋙ classifyingFundamentalGroupoidFunctor D) X) := by
  subst d
  rw [E.qObjectClass_natIso (classifyingFundamentalGroupoidNaturality F) X]
  erw [← Iso.trans_conj, E.qObjectClass_comp]
  apply congrArg₂ (fun (e : FundamentalGroupoid.mk
      ((classifyingSpaceMap F).hom (classifyingSpacePoint E.qZero)) ≅
        FundamentalGroupoid.mk (classifyingSpacePoint (F.obj E.qZero)))
      (a : End (FundamentalGroupoid.mk ((classifyingSpaceMap F).hom (classifyingSpacePoint
        E.qZero)))) => e.conj a)
  · apply Iso.ext
    dsimp [classifyingFundamentalGroupoidNaturality, classifyingFundamentalGroupoidFunctor,
      eqToIso]
    simp only [classifyingSpacePath_id, Path.Homotopic.Quotient.mk_refl]
    change eqToHom _ = eqToHom _ ≫ 𝟙 _
    simp
  · rfl

/-- Rebasing a Q-functor replaces transport along a categorical isomorphism
by transport along the resulting literal basepoint equality. -/
lemma rebase_qObjectClass {D : Type u} {T : Type*} [Category.{max u v} D] [Groupoid T]
    (F : E.QCategory ⥤ D) (d : D) (e : F.obj E.qZero ≅ d)
    (H : D ⥤ T) (X : C) :
    (H.mapIso (eqToIso (rebaseFunctor_obj_base F E.qZero d e))).conj
      (E.qObjectClass (rebaseFunctor F E.qZero d e ⋙ H) X) =
    (H.mapIso e).conj (E.qObjectClass (F ⋙ H) X) := by
  rw [E.qObjectClass_natIso (Functor.isoWhiskerRight (rebaseFunctorIso F E.qZero d e) H) X]
  erw [← Iso.trans_conj]
  congr 1
  apply congrArg Iso.conj
  apply Iso.ext
  change H.map ((rebaseFunctorIso F E.qZero d e).hom.app E.qZero) ≫
      H.map (eqToHom (rebaseFunctor_obj_base F E.qZero d e)) = H.map e.hom
  rw [← H.map_comp, rebaseFunctorIso_hom_base]
  simp

/-- Maps from the multiplicative Grothendieck group into any group are
determined by the object generators; commutativity of the target is unnecessary. -/
@[ext] lemma grothendieck_mulHom_ext {G : Type*} [Group G]
    (f g : Multiplicative E.GrothendieckGroup →* G)
    (h : ∀ X, f (Multiplicative.ofAdd (E.grothendieckClass X)) =
      g (Multiplicative.ofAdd (E.grothendieckClass X))) : f = g := by
  apply MonoidHom.ext
  intro a
  change f (Multiplicative.ofAdd a.toAdd) = g (Multiplicative.ofAdd a.toAdd)
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective E.grothendieckRelations a.toAdd
  rw [← hr]
  clear hr a
  induction r using FreeAbelianGroup.induction_on with
  | zero => simp
  | of X => exact h X
  | neg r ih =>
      simp only [map_neg, ofAdd_neg, map_inv, ih]
  | add r s hr hs =>
      simp only [map_add, ofAdd_add, map_mul, hr, hs]

end CategoryTheory.ExactCategory.ExactStructure

namespace Quillen
end Quillen

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The exact Q-functor preserves zero-apex arrows after the canonical
zero-object isomorphism. -/
lemma mapQ_fromZero (F : ExactFunctor EC ED) (X : C) :
    (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZero (Q.of ED.deflation ED.inflation (F.toFunctor.obj X)) =
      F.mapQ.map (EC.fromZero (Q.of EC.deflation EC.inflation X)) := by
  let e := F.toFunctor.mapZeroObject
  change Q.mkHom ED.deflation ED.inflation (Q.isoSpan _ _ e _) ≫
    Q.mkHom ED.deflation ED.inflation _ = Q.mkHom ED.deflation ED.inflation _
  have h : IsPullback (𝟙 (F.toFunctor.obj (0 : C))) e.hom e.hom (𝟙 (0 : D)) :=
    IsPullback.of_horiz_isIso ⟨by exact Subsingleton.elim _ _⟩
  apply ED.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QCompatibleFunctor.mapSpan, Q.isoSpan, Q.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
    simpa using F.toFunctor.mapZeroObject.hom_inv_id
  · simp [QCompatibleFunctor.mapSpan, Q.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]

/-- The exact Q-functor preserves whole-apex arrows with the same canonical
zero-object comparison. -/
lemma mapQ_fromZeroTotal (F : ExactFunctor EC ED) (X : C) :
    (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZeroTotal (Q.of ED.deflation ED.inflation (F.toFunctor.obj X)) =
      F.mapQ.map (EC.fromZeroTotal (Q.of EC.deflation EC.inflation X)) := by
  let e := F.toFunctor.mapZeroObject
  change Q.mkHom ED.deflation ED.inflation (Q.isoSpan _ _ e _) ≫
    Q.mkHom ED.deflation ED.inflation _ = Q.mkHom ED.deflation ED.inflation _
  have h : IsPullback (0 : F.toFunctor.obj X ⟶ F.toFunctor.obj (0 : C))
      (𝟙 (F.toFunctor.obj X)) e.hom (0 : F.toFunctor.obj X ⟶ 0) :=
    (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  apply ED.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QCompatibleFunctor.mapSpan, Q.isoSpan, Q.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]
  · simp [QCompatibleFunctor.mapSpan, Q.of,
    CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor]

/-- Canonical object classes are natural for exact functors in every groupoid
image, after conjugation by exactly the chosen zero-object isomorphism. -/
lemma qObjectClass_mapQ {T : Type*} [Groupoid T] (F : ExactFunctor EC ED)
    (H : ED.QCategory ⥤ T) (X : C) :
    (H.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject)).conj
        (EC.qObjectClass (F.mapQ ⋙ H) X) =
      ED.qObjectClass H (F.toFunctor.obj X) := by
  simp only [Iso.conj_apply, CategoryTheory.ExactCategory.ExactStructure.qObjectClass,
    Functor.comp_map,
    Functor.mapIso_inv, Functor.mapIso_hom]
  rw [← F.mapQ_fromZeroTotal X]
  simp only [← Groupoid.inv_eq_inv]
  rw [← F.mapQ_fromZero X]
  simp [Category.assoc, Groupoid.inv_eq_inv]

/-- The exact-functor K-map carries every canonical object loop to the loop
of its image object. This uses the same zero normalization as `KMap`. -/
@[simp] theorem KMap_kZeroObjectClass (F : ExactFunctor EC ED) (X : C) :
    F.KMap 0 (EC.kZeroObjectClass X) = ED.kZeroObjectClass (F.toFunctor.obj X) := by
  let e := ED.qIsoOfIso F.toFunctor.mapZeroObject
  let G := rebaseFunctor F.mapQ EC.qZero ED.qZero e
  have hG : G.obj EC.qZero = ED.qZero := rebaseFunctor_obj_base F.mapQ EC.qZero ED.qZero e
  apply ED.kZeroFundamentalGroupEquiv.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (homotopyGroupMap (classifyingSpaceMap G).hom
      ((classifyingSpaceMap_point G EC.qZero).trans (congrArg classifyingSpacePoint hG))
      (EC.kZeroObjectClass X)) = _
  rw [pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (EC.kZeroFundamentalGroupEquiv (EC.kZeroObjectClass X)) = _
  rw [EC.kZeroFundamentalGroupEquiv_objectClass, ED.kZeroFundamentalGroupEquiv_objectClass,
    EC.kZeroObjectLoop_eq_qObjectClass, ED.kZeroObjectLoop_eq_qObjectClass]
  erw [EC.fundamentalMap_qObjectClass G ED.qZero hG X,
    EC.rebase_qObjectClass F.mapQ ED.qZero e _ X]
  exact F.qObjectClass_mapQ _ X

/-- The algebraic-to-homotopical K₀ comparison is natural for every exact
functor, with the canonical maps already used elsewhere in the project. -/
theorem grothendieckToKZero_naturality (F : ExactFunctor EC ED) :
    (F.KMap 0).comp EC.grothendieckToKZero =
      ED.grothendieckToKZero.comp F.grothendieckMap.toMultiplicative := by
  apply EC.grothendieck_mulHom_ext
  intro X
  simp

end CategoryTheory.ExactCategory.ExactFunctor

namespace Quillen
end Quillen
