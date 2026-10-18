/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Automorphism.Universal
public import Quillen.KTheory.Automorphism.PositiveNormalization
public import Quillen.KTheory.Field.MatrixTransport
public import Quillen.KTheory.Field.StableMatrixMarking
public import Quillen.KTheory.Field.ModuleDeterminant
public import Quillen.KTheory.Map.UniverseComparison

/-!
# Positive matrix cubes under the original upper finite-module comparison

The canonical right-projective comparison, including the inverse of the actual
SmallModel realization equivalence, carries the positive normalized universal
core edge to the literal old automorphism-first cube. The original rank-one-power
coordinates then give the standard matrix action with the same matrix.

The proof extends the existing cone and capped-class naturality argument to the
specific mixed universes of the projective and upper finite-module categories.
It uses the original Q-functor, its canonical zero isomorphism, and the existing
Q rebasing. The original group objects and comparison maps are unchanged.

The completion marking theorem and the existing determinant comparison therefore
mark the literal finite-matrix cube by its ordinary determinant. The hypotheses
are only that the coefficient ring is a field; every finite rank, including
zero, is covered.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject Topology

namespace Quillen.Automorphism.MatrixComparison
universe w v
private def edgeCoreEnd {T : Type w} [Category.{v} T] (A : T) : Aut A →* End (Core.mk A) where
  toFun α := CoreHom.mk α
  map_one' := rfl
  map_mul' _ _ := rfl

private def edgeClass {T : Type w} [Category.{v} T] [Preadditive T] [HasFiniteBiproducts T]
    (E : ExactStructure T) (A : T) : Aut A →* E.K 1 :=
  (loopComponentToPiTwo (universalCoreLoopMap E (classifyingSpacePoint (Core.mk A)))).comp
    ((FundamentalGroup.map (universalCoreLoopMap E) (classifyingSpacePoint (Core.mk A))).comp
      (((classifyingFundamentalGroupoidFunctor (Core T)).mapEnd (Core.mk A)).comp
        (edgeCoreEnd A)))

private theorem edgeClass_eq {T : Type w} [Category.{v} T] [Preadditive T] [HasFiniteBiproducts T]
    (E : ExactStructure T) (A : T) (α : Aut A) :
    edgeClass E A α = loopComponentToPiTwo (universalCoreLoopMap E (classifyingSpacePoint
      (Core.mk A)))
      (Path.Homotopic.Quotient.mk ((classifyingSpacePath
        (CoreHom.mk α : Core.mk A ⟶ Core.mk A)).map (universalCoreLoopMap E).continuous)) := rfl

private theorem correctedMap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f = g) {x : X} {y : Y}
    (p : Path (f x) y) (q : Path (g x) y) (hpq : ∀ t, p t = q t)
    (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport p n (homotopyGroupMap f rfl a) =
      pathTransport q n (homotopyGroupMap g rfl a) := by
  subst g
  have he : p = q := Path.ext (funext hpq)
  subst q
  rfl

variable {C D : Type (u + 1)} [Category.{u} C] [SmallCategory D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

private abbrev normalized := rebaseFunctor F.mapQ EC.qZero ED.qZero
  (ED.qIsoOfIso F.toFunctor.mapZeroObject)

private lemma normalized_point :
    classifyingSpaceMap (normalized F) EC.kBasepoint = ED.kBasepoint :=
  rebaseFunctor_map_point _ _ _ _

private theorem universalKMap_normalized (n : ℕ) :
    F.universalKMap n = piMap n (classifyingSpaceMap (normalized F)).hom
      (normalized_point F) := by
  ext a
  change pathTransport (F.universalQZeroBasePath) (n + 1)
    (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a) = _
  change pathTransport F.universalQZeroBasePath (n + 1)
    (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a) =
    homotopyGroupMap (classifyingSpaceMap (normalized F)).hom (normalized_point F) a
  exact (correctedMap_congr (classifyingSpaceMapUniversal_eq F.mapQ)
    F.universalQZeroBasePath
    (classifyingSpaceIsoBasePath F.mapQ EC.qZero ED.qZero
      (ED.qIsoOfIso F.toFunctor.mapZeroObject)) (fun _ => rfl) (n + 1) a).trans
      (pathTransport_rebaseFunctor_homotopyGroupMap F.mapQ EC.qZero ED.qZero
        (ED.qIsoOfIso F.toFunctor.mapZeroObject) (n + 1) a)

private theorem mapQ_iso {X Y : C} (e : X ≅ Y) :
    F.mapQ.mapIso (EC.qIsoOfIso e) = ED.qIsoOfIso (F.toFunctor.mapIso e) := by
  apply Iso.ext
  apply Quotient.sound
  refine ⟨Span.mkIso (Iso.refl _) ?_ ?_⟩
  · change 𝟙 (F.toFunctor.obj X) ≫ 𝟙 (F.toFunctor.obj X) = F.toFunctor.map (𝟙 X)
    simp
  · change 𝟙 (F.toFunctor.obj X) ≫ F.toFunctor.map e.hom = F.toFunctor.map e.hom
    simp

private theorem mapQ_zero (A : C) :
    F.mapQ.map (EC.fromZero (Q.of _ _ A)) =
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫ ED.fromZero (Q.of _ _ (F.toFunctor.obj A))
        := by
  let e := F.toFunctor.mapZeroObject
  let sq : IsPullback (𝟙 (F.toFunctor.obj (0 : C))) e.hom e.hom (𝟙 (0 : D)) :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
  let : HasPullback e.hom (𝟙 (0 : D)) := sq.hasPullback
  apply Q.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = F.toFunctor.map (𝟙 (0 : C))
    simp only [Category.comp_id, IsPullback.isoPullback_hom_fst, F.toFunctor.map_id]
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ 0 = F.toFunctor.map (0 : (0 : C) ⟶ A)
    simp

private theorem mapQ_full (A : C) :
    F.mapQ.map (fullFromZero EC A) =
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫ fullFromZero ED (F.toFunctor.obj A) := by
  let e := F.toFunctor.mapZeroObject
  let sq : IsPullback (0 : F.toFunctor.obj A ⟶ F.toFunctor.obj (0 : C))
      (𝟙 (F.toFunctor.obj A)) e.hom (0 : F.toFunctor.obj A ⟶ (0 : D)) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  let : HasPullback e.hom (0 : F.toFunctor.obj A ⟶ (0 : D)) := sq.hasPullback
  apply Q.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = F.toFunctor.map (0 : A ⟶ (0 : C))
    simp
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ 𝟙 _ = F.toFunctor.map (𝟙 A)
    simp

private lemma normalized_zero : (normalized F).obj EC.qZero = ED.qZero :=
  rebaseFunctor_obj_base _ _ _ _

private lemma qObj_ne_zero (A : C) (hA : A ≠ 0) : Q.of EC.deflation EC.inflation A ≠ EC.qZero := by
  intro h
  exact hA (congrArg (fun X : EC.QCategory => X.obj.of) h)

private lemma normalized_obj (A : C) (hA : A ≠ 0) :
    (normalized F).obj (Q.of EC.deflation EC.inflation A) =
      Q.of ED.deflation ED.inflation (F.toFunctor.obj A) := by
  classical
  simp only [normalized, rebaseFunctor, rebaseObj, ite_eq_right (qObj_ne_zero (EC := EC) A hA)]
  rfl

private theorem normalized_zeroArm (A : C) (hA : A ≠ 0) :
    eqToHom (normalized_zero F).symm ≫
      (normalized F).map (EC.fromZero (Q.of _ _ A)) ≫ eqToHom (normalized_obj F A hA) =
      ED.fromZero (Q.of _ _ (F.toFunctor.obj A)) := by
  classical
  simp only [rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [mapQ_zero]
  simp

private theorem normalized_fullArm (A : C) (hA : A ≠ 0) :
    eqToHom (normalized_zero F).symm ≫
      (normalized F).map (fullFromZero EC A) ≫ eqToHom (normalized_obj F A hA) =
      fullFromZero ED (F.toFunctor.obj A) := by
  classical
  simp only [rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [mapQ_full]
  simp

private theorem normalized_automorphism (A : C) (hA : A ≠ 0) (α : Aut A) :
    eqToHom (normalized_obj F A hA).symm ≫
      (normalized F).map (EC.qIsoOfIso α).hom ≫ eqToHom (normalized_obj F A hA) =
      (ED.qIsoOfIso (F.toFunctor.mapIso α)).hom := by
  classical
  simp only [rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact congrArg Iso.hom (mapQ_iso F α)

private def autCore (A : C) : SingleObj (Aut A) ⥤ Core C :=
  SingleObj.functor (edgeCoreEnd A)

private def imageAutCore (A : C) : SingleObj (Aut A) ⥤ Core D :=
  SingleObj.functor ((edgeCoreEnd (F.toFunctor.obj A)).comp (F.toFunctor.mapAut A))

private lemma row_eq (A : C) (hA : A ≠ 0) :
    (autCore A ⋙ coreQ EC) ⋙ normalized F = imageAutCore F A ⋙ coreQ ED := by
  refine CategoryTheory.Functor.ext (fun _ => normalized_obj F A hA) ?_
  intro X Y α
  apply (cancel_epi (eqToHom (normalized_obj F A hA).symm)).mp
  apply (cancel_mono (eqToHom (normalized_obj F A hA))).mp
  simp only [Functor.comp_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  change eqToHom (normalized_obj F A hA).symm ≫
    (normalized F).map (EC.qIsoOfIso α).hom ≫ eqToHom (normalized_obj F A hA) =
    (ED.qIsoOfIso (F.toFunctor.mapIso α)).hom
  exact normalized_automorphism F A hA α

private lemma const_eq (A : C) :
    (autCore A ⋙ (Functor.const (Core C)).obj EC.qZero) ⋙ normalized F =
      imageAutCore F A ⋙ (Functor.const (Core D)).obj ED.qZero := by
  refine CategoryTheory.Functor.ext (fun _ => normalized_zero F) ?_
  intro X Y α
  simp

private lemma zeroCone_eq (A : C) (hA : A ≠ 0) :
    Functor.whiskerRight (Functor.whiskerLeft (autCore A) (zeroCone EC)) (normalized F) ≫
        eqToHom (row_eq F A hA) =
      eqToHom (const_eq F A) ≫
        Functor.whiskerLeft (imageAutCore F A) (zeroCone ED) := by
  apply NatTrans.ext
  funext X
  apply (cancel_epi (eqToHom (normalized_zero F).symm)).mp
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, zeroCone, imageAutCore, Functor.comp_obj, SingleObj.functor_obj,
      autCore, SingleObj.functor_obj, coreQ, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using normalized_zeroArm F A hA

private lemma fullCone_eq (A : C) (hA : A ≠ 0) :
    Functor.whiskerRight (Functor.whiskerLeft (autCore A) (fullCone EC)) (normalized F) ≫
        eqToHom (row_eq F A hA) =
      eqToHom (const_eq F A) ≫
        Functor.whiskerLeft (imageAutCore F A) (fullCone ED) := by
  apply NatTrans.ext
  funext X
  apply (cancel_epi (eqToHom (normalized_zero F).symm)).mp
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, fullCone, imageAutCore, Functor.comp_obj, SingleObj.functor_obj,
      autCore, SingleObj.functor_obj, coreQ, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using normalized_fullArm F A hA

private theorem transformation_congr {B T : Type*} [Category B] [Category T]
    {K L K' L' : B ⥤ T} (hK : K = K') (hL : L = L')
    (α : K ⟶ L) (β : K' ⟶ L')
    (hα : α ≫ eqToHom hL = eqToHom hK ≫ β)
    (t : unitInterval) (x : ClassifyingSpace B) :
    classifyingSpaceUniversalHomotopy α (t, x) =
      classifyingSpaceUniversalHomotopy β (t, x) := by
  subst K'
  subst L'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hα
  subst β
  rfl

private theorem zeroCone_realized (A : C) (hA : A ≠ 0)
    (t : unitInterval) (x : ClassifyingSpace (SingleObj (Aut A))) :
    classifyingSpaceMap (normalized F)
      (classifyingSpaceUniversalHomotopy (zeroCone EC)
        (t, classifyingSpaceMapUniversal (autCore A) x)) =
      classifyingSpaceUniversalHomotopy (zeroCone ED)
        (t, classifyingSpaceMapUniversal (imageAutCore F A) x) := by
  have H := transformation_congr (const_eq F A) (row_eq F A hA)
    (Functor.whiskerRight (Functor.whiskerLeft (autCore A) (zeroCone EC)) (normalized F))
    (Functor.whiskerLeft (imageAutCore F A) (zeroCone ED))
    (zeroCone_eq F A hA) t x
  simpa only [universalHomotopy_whiskerRight, universalHomotopy_whiskerLeft,
    classifyingSpaceMapUniversal_eq] using H

private theorem fullCone_realized (A : C) (hA : A ≠ 0)
    (t : unitInterval) (x : ClassifyingSpace (SingleObj (Aut A))) :
    classifyingSpaceMap (normalized F)
      (classifyingSpaceUniversalHomotopy (fullCone EC)
        (t, classifyingSpaceMapUniversal (autCore A) x)) =
      classifyingSpaceUniversalHomotopy (fullCone ED)
        (t, classifyingSpaceMapUniversal (imageAutCore F A) x) := by
  have H := transformation_congr (const_eq F A) (row_eq F A hA)
    (Functor.whiskerRight (Functor.whiskerLeft (autCore A) (fullCone EC)) (normalized F))
    (Functor.whiskerLeft (imageAutCore F A) (fullCone ED))
    (fullCone_eq F A hA) t x
  simpa only [universalHomotopy_whiskerRight, universalHomotopy_whiskerLeft,
    classifyingSpaceMapUniversal_eq] using H

private theorem coreLoop_realized (A : C) (hA : A ≠ 0)
    (x : ClassifyingSpace (SingleObj (Aut A))) :
    basedLoopMap (classifyingSpaceMap (normalized F)).hom (normalized_point F)
      (universalCoreLoopMap EC (classifyingSpaceMapUniversal (autCore A) x)) =
      universalCoreLoopMap ED (classifyingSpaceMapUniversal (imageAutCore F A) x) := by
  ext t
  change classifyingSpaceMap (normalized F)
    (((ConePair.realizedCone (zeroCone EC)).evalAt _).trans
      ((ConePair.realizedCone (fullCone EC)).evalAt _).symm t) =
    (((ConePair.realizedCone (zeroCone ED)).evalAt _).trans
      ((ConePair.realizedCone (fullCone ED)).evalAt _).symm t)
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact zeroCone_realized F A hA _ x
  · exact fullCone_realized F A hA _ x

private theorem coreLoop_vertex (A : C) (hA : A ≠ 0) :
    basedLoopMap (classifyingSpaceMap (normalized F)).hom (normalized_point F)
      (universalCoreLoopMap EC (classifyingSpacePoint (Core.mk A))) =
      universalCoreLoopMap ED (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))) := by
  simpa only [classifyingSpaceMapUniversal_point, autCore, SingleObj.functor_obj,
    imageAutCore, Functor.comp_obj, SingleObj.functor_obj] using
      coreLoop_realized F A hA (classifyingSpacePoint (SingleObj.star (Aut A)))

private theorem coreLoop_cylinder (A : C) (hA : A ≠ 0) (α : Aut A) (s : unitInterval) :
    basedLoopMap (classifyingSpaceMap (normalized F)).hom (normalized_point F)
      (universalCoreLoopMap EC (classifyingSpacePath
        (CoreHom.mk α : Core.mk A ⟶ Core.mk A) s)) =
      universalCoreLoopMap ED (classifyingSpacePath
        (CoreHom.mk (F.toFunctor.mapIso α) : Core.mk (F.toFunctor.obj A) ⟶ _) s) := by
  have H := coreLoop_realized F A hA (classifyingSpacePath
    (SingleObj.toEnd (Aut A) α) s)
  simp only [classifyingSpaceMapUniversal_path] at H
  change basedLoopMap (classifyingSpaceMap (normalized F)).hom (normalized_point F)
      (universalCoreLoopMap EC (classifyingSpacePath
        (CoreHom.mk α : Core.mk A ⟶ Core.mk A) s)) =
      universalCoreLoopMap ED (classifyingSpacePath
        (CoreHom.mk (F.toFunctor.mapIso α) : Core.mk (F.toFunctor.obj A) ⟶ _) s) at H
  exact H

set_option backward.isDefEq.respectTransparency true in
private theorem edgeClass_natural (A : C) (α : Aut A) :
    F.universalKMap 1 (edgeClass EC A α) = edgeClass ED (F.toFunctor.obj A) (F.toFunctor.mapIso
      α) := by
  classical
  by_cases hA : A = 0
  · have hZ : IsZero A := hA ▸ isZero_zero C
    have hα : α = 1 := Iso.ext (hZ.eq_of_src α.hom (𝟙 A))
    rw [hα, map_one, map_one]
    have he : F.toFunctor.mapIso (1 : Aut A) = (1 : Aut (F.toFunctor.obj A)) :=
      F.toFunctor.mapIso_refl A
    rw [he, map_one]
  · rw [edgeClass_eq, edgeClass_eq, universalKMap_normalized]
    let p : Path EC.kBasepoint EC.kBasepoint :=
      universalCoreLoopMap EC (classifyingSpacePoint (Core.mk A))
    let q : Path p p := (classifyingSpacePath
      (CoreHom.mk α : Core.mk A ⟶ Core.mk A)).map (universalCoreLoopMap EC).continuous
    let f : C(EC.KSpace, ED.KSpace) := (classifyingSpaceMap (normalized F)).hom
    have hf : f EC.kBasepoint = ED.kBasepoint := normalized_point F
    have hn := Cap.loopComponentToPiTwo_natural
      (X := EC.KSpace) (Y := ED.KSpace) (x := EC.kBasepoint) (y := ED.kBasepoint)
      f hf p (Path.Homotopic.Quotient.mk q)
    refine hn.trans ?_
    change loopComponentToPiTwo _
      (Path.Homotopic.Quotient.mk (q.map (basedLoopMap f hf).continuous)) = _
    apply Functoriality.componentToPiTwo_congr (coreLoop_vertex F A hA)
    exact coreLoop_cylinder F A hA α

private theorem edgeClass_small (A : D) (α : Aut A) : edgeClass ED A α = automorphismClass ED A
  α := by
  unfold edgeClass automorphismClass
  rw [universalCoreLoopMap_eq ED]
  rfl

private theorem positiveCore_edge {B : Type w} [Category.{v} B]
    (K : B ⥤ Core C) (b : B) (γ : b ⟶ b) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv
        (positiveNormalizationPath ((universalCoreLoopMap EC).comp (classifyingSpaceMapUniversal K))
          (classifyingSpacePoint b)) 0
        (piMap 0 (positiveNormalizedLoopMap
          ((universalCoreLoopMap EC).comp (classifyingSpaceMapUniversal K))
          (classifyingSpacePoint b)) rfl
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
            (Path.Homotopic.Quotient.mk (classifyingSpacePath γ))))) =
      (edgeClass EC (K.obj b).of (K.map γ).iso)⁻¹ := by
  rw [positiveNormalization_formula, MulEquiv.apply_symm_apply, edgeClass_eq]
  apply congrArg (fun a => a⁻¹)
  have hp : ((universalCoreLoopMap EC).comp (classifyingSpaceMapUniversal K))
      (classifyingSpacePoint b) =
      universalCoreLoopMap EC (classifyingSpacePoint (Core.mk (K.obj b).of)) := by
    change universalCoreLoopMap EC (classifyingSpaceMapUniversal K (classifyingSpacePoint b)) = _
    rw [classifyingSpaceMapUniversal_point]
  change loopComponentToPiTwo _
    (Path.Homotopic.Quotient.mk ((classifyingSpacePath γ).map
      ((universalCoreLoopMap EC).comp (classifyingSpaceMapUniversal K)).continuous)) = _
  apply Functoriality.componentToPiTwo_congr hp
  intro t
  change universalCoreLoopMap EC (classifyingSpaceMapUniversal K (classifyingSpacePath γ t)) = _
  rw [classifyingSpaceMapUniversal_path]
  rfl

private theorem positiveCore_edge_cube {B : Type w} [Category.{v} B]
    (K : B ⥤ Core C) (b : B) (γ : b ⟶ b) :
    F.universalKMap 1 ((loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv
        (positiveNormalizationPath ((universalCoreLoopMap EC).comp (classifyingSpaceMapUniversal K))
          (classifyingSpacePoint b)) 0
        (piMap 0 (positiveNormalizedLoopMap
          ((universalCoreLoopMap EC).comp (classifyingSpaceMapUniversal K))
          (classifyingSpacePoint b)) rfl
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
            (Path.Homotopic.Quotient.mk (classifyingSpacePath γ)))))) =
      (Quotient.mk' (Cube.automorphismFirstCube ED (F.toFunctor.obj (K.obj b).of)
        (F.toFunctor.mapIso (K.map γ).iso)) : ED.K 1) := by
  have h := congrArg (fun a : EC.K 1 => F.universalKMap 1 a)
    (positiveCore_edge (EC := EC) K b γ)
  refine h.trans ?_
  rw [map_inv, edgeClass_natural F, edgeClass_small, Cube.automorphismFirstCube_class]

end Quillen.Automorphism.MatrixComparison

namespace Quillen.Field

private theorem universalKMap_commonAmbient {C D : Type (u + 1)} [SmallCategory C] [Category.{u} D]
    [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
    {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED) (n : ℕ) :
    F.universalKMap n = F.commonAmbientKMap n := by
  ext a
  change pathTransport (F.universalQZeroBasePath) (n + 1)
    (homotopyGroupMap (classifyingSpaceMapUniversal F.mapQ) rfl a) =
    homotopyGroupMap (classifyingSpaceMap F.commonAmbientNormalizedQ).hom
      F.commonAmbientNormalizedQ_map_point a
  exact (Automorphism.MatrixComparison.correctedMap_congr (classifyingSpaceMapUniversal_eq F.mapQ)
    F.universalQZeroBasePath
    (classifyingSpaceIsoBasePath F.mapQ EC.qZero ED.qZero
      (ED.qIsoOfIso F.toFunctor.mapZeroObject)) (fun _ => rfl) (n + 1) a).trans
      (pathTransport_rebaseFunctor_homotopyGroupMap F.mapQ EC.qZero ED.qZero
        (ED.qIsoOfIso F.toFunctor.mapZeroObject) (n + 1) a)

private theorem toSmallModel_then_original {C : Type (u + 1)} [Category.{u} C]
    [Preadditive C] [HasFiniteBiproducts C] [EssentiallySmall.{u + 1} C]
    (E : ExactStructure C) (n : ℕ) (a : E.K n) :
    E.smallModelToOriginal.{u + 1}.commonAmbientKMap n
      (E.originalToSmallModel.{u + 1}.universalKMap n a) = a := by
  rw [← universalKMap_commonAmbient]
  change ((E.smallModelToOriginal.{u + 1}.universalKMap n).comp
    (E.originalToSmallModel.{u + 1}.universalKMap n)) a = a
  rw [← ExactFunctor.universalKMap_comp]
  have e : (E.originalToSmallModel.{u + 1}.comp E.smallModelToOriginal.{u + 1}).toFunctor ≅
      (ExactFunctor.id E).toFunctor := (equivSmallModel.{u + 1} C).unitIso.symm
  rw [ExactFunctor.universalKMap_eq_of_natIso e n, ExactFunctor.universalKMap_eq_KMap,
    ExactFunctor.KMap_id]
  rfl

/-- The actual projective inclusion and opposite-ring restriction, followed by the chosen upper
  model. -/
def rightProjectiveToUpperExact (F : Type u) [Field F] :
    ExactFunctor (FiniteProjectiveModule.exactStructure Fᵐᵒᵖ)
      (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1} :=
  (rightProjectiveToModuleExact F).comp
    (ModuleCat.finiteModuleExactStructure.{u, u} F).originalToSmallModel.{u + 1}

/-- This exact composite induces the specified comparison with its actual SmallModel inverse. -/
theorem rightProjectiveToUpperExact_universalKMap (F : Type u) [Field F] (n : ℕ)
    (a : (FiniteProjectiveModule.exactStructure Fᵐᵒᵖ).K n) :
    (rightProjectiveToUpperExact F).universalKMap n a = rightProjectiveUpperModuleKEquiv F n a := by
  apply ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u +
    1}.commonAmbientKEquiv n).injective
  change (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u +
    1}.commonAmbientKMap n
      ((rightProjectiveToUpperExact F).universalKMap n a) =
    (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u + 1}.commonAmbientKMap n
      (rightProjectiveUpperModuleKEquiv F n a)
  rw [rightProjectiveUpperModuleKEquiv_toOriginal]
  rw [rightProjectiveToUpperExact, ExactFunctor.universalKMap_comp]
  change (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModelToOriginal.{u +
    1}.commonAmbientKMap n
      ((ModuleCat.finiteModuleExactStructure.{u, u} F).originalToSmallModel.{u + 1}.universalKMap n
        ((rightProjectiveToModuleExact F).universalKMap n a)) = _
  rw [toSmallModel_then_original]
  change ((FiniteProjectiveModule.toFiniteModuleExact Fᵐᵒᵖ).comp
      (finiteModuleRingExact (RingEquiv.toOpposite F))).universalKMap n a = _
  rw [ExactFunctor.universalKMap_comp, ExactFunctor.universalKMap_eq_KMap,
    ExactFunctor.universalKMap_eq_KMap]
  rfl

variable (F : Type u) [Field F]

/-- The positive universal core edge becomes the literal cube of the original mapped power
  action. -/
theorem rightProjectiveUpperModuleKEquiv_positiveCore_powerCube (n : ℕ)
    (g : StableGeneralLinear.GL F n) :
    rightProjectiveUpperModuleKEquiv F 1
      ((loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv
          (Automorphism.positiveNormalizationPath (FiniteProjectiveModule.stageCoreLoopMap F n)
            (classifyingSpacePoint (FiniteProjectiveModule.stageVertex F n))) 0
          (piMap 0
            (Automorphism.positiveNormalizedLoopMap (FiniteProjectiveModule.stageCoreLoopMap F n)
              (classifyingSpacePoint (FiniteProjectiveModule.stageVertex F n))) rfl
                (FiniteProjectiveModule.finiteMatrixPiOne F n g)))) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          ((rightProjectiveToModuleExact F).toFunctor.obj
            (FiniteProjectiveModule.rankOnePower Fᵐᵒᵖ n).of))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          ((rightProjectiveToModuleExact F).toFunctor.mapIso
            (FiniteProjectiveModule.StableFree.powerEndEquiv F n g).iso))) :
          (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) := by
  rw [← rightProjectiveToUpperExact_universalKMap]
  exact Automorphism.MatrixComparison.positiveCore_edge_cube
    (rightProjectiveToUpperExact F) (FiniteProjectiveModule.stageCore F n)
    (FiniteProjectiveModule.stageVertex F n)
    (AsSmall.up.map (SingleObj.toEnd (StableGeneralLinear.GL F n) g))

/-- The same positive class becomes the old cube of the standard matrix action with unchanged
  matrix. -/
theorem rightProjectiveUpperModuleKEquiv_positiveCore_matrixCube (n : ℕ)
    (g : StableGeneralLinear.GL F n) :
    rightProjectiveUpperModuleKEquiv F 1
      ((loopShiftMulEquiv 0).symm
        (pathTransportMulEquiv
          (Automorphism.positiveNormalizationPath (FiniteProjectiveModule.stageCoreLoopMap F n)
            (classifyingSpacePoint (FiniteProjectiveModule.stageVertex F n))) 0
          (piMap 0
            (Automorphism.positiveNormalizedLoopMap (FiniteProjectiveModule.stageCoreLoopMap F n)
              (classifyingSpacePoint (FiniteProjectiveModule.stageVertex F n))) rfl
                (FiniteProjectiveModule.finiteMatrixPiOne F n g)))) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          (FGModuleCat.of F (Fin n → F)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          (FGModuleCat.matrixToAut F n g))) :
            (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) :=
  (rightProjectiveUpperModuleKEquiv_positiveCore_powerCube F n g).trans
    (upperPowerMatrixCube_class F n g)

/-- The original elementary quotient comparison marks the literal standard finite-matrix cube. -/
theorem elementaryUpperModuleKOneEquiv_matrix_cube (n : ℕ)
    (g : StableGeneralLinear.GL F n) :
    elementaryUpperModuleKOneEquiv F
      (StableGeneralLinear.quotientMap F (StableGeneralLinear.of F n g)) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          (FGModuleCat.of F (Fin n → F)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          (FGModuleCat.matrixToAut F n g))) :
            (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) := by
  change rightProjectiveUpperModuleKEquiv F 1
    (FiniteProjectiveModule.StableCompletion.elementaryProjectiveKOneEquiv F
      (StableGeneralLinear.quotientMap F (StableGeneralLinear.of F n g))) = _
  rw [FiniteProjectiveModule.elementaryProjectiveKOneEquiv_matrix_positiveCore]
  exact rightProjectiveUpperModuleKEquiv_positiveCore_matrixCube F n g

/-- The original zero-completion class maps to the literal standard finite-matrix cube. -/
theorem rightProjectiveUpperModuleKEquiv_matrix_cube (n : ℕ)
    (g : StableGeneralLinear.GL F n) :
    rightProjectiveUpperModuleKEquiv F 1
      (FiniteProjectiveModule.StableCompletion.zeroCompletionPositiveKEquiv F 0
        (FiniteProjectiveModule.StableCompletion.stableGroupPiOneMap F
          (StableGeneralLinear.of F n g))) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          (FGModuleCat.of F (Fin n → F)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          (FGModuleCat.matrixToAut F n g))) :
            (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) :=
  (elementaryUpperModuleKOneEquiv_quotientMap F (StableGeneralLinear.of F n g)).symm.trans
    (elementaryUpperModuleKOneEquiv_matrix_cube F n g)

/-- The unchanged module determinant sends the actual old finite-matrix cube to its ordinary
  determinant. -/
theorem moduleDetEquiv_matrix_cube (n : ℕ) (g : StableGeneralLinear.GL F n) :
    moduleDetEquiv F
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          (FGModuleCat.of F (Fin n → F)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          (FGModuleCat.matrixToAut F n g)))) = Matrix.GeneralLinearGroup.det g := by
  rw [← rightProjectiveUpperModuleKEquiv_matrix_cube]
  exact moduleDetEquiv_matrix F n g

end Quillen.Field
