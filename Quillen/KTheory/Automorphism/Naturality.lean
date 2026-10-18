/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Automorphism.Class
public import Quillen.KTheory.Map.NaturalIso

/-!
# Naturality of the original Q automorphism cylinder and cap

Pointed continuous maps preserve the literal cap. The genuine normalized
Q-functor preserves the zero and full cone arms and the automorphism cylinder,
which proves exact-functor naturality of the original Q automorphism class.
These are the corresponding R5 cylinder proofs at revision
`1b7c3945394bcc27a94d1ebf86df702b0291ee18`, with their mathematical terms retained.
-/
@[expose] public section
open CategoryTheory.ExactCategory (ExactFunctor ExactStructure)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open Quillen Quillen.Automorphism
open scoped Topology unitInterval

namespace Quillen.Automorphism.Cap
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Explicit based loop of loops closing the automorphism cylinder. -/
def cappedLoop (p : Path x x) (q : Path p p) : Path (Path.refl x) (Path.refl x) :=
  (cancellationPath p).trans ((q.map (rightTranslate p).continuous).trans (cancellationPath p).symm)

/-- Unpack the two quotient comparisons into one actual based two-cube. -/
theorem componentToPiTwo_eq_cube (p : Path x x) (q : Path p p) :
    loopComponentToPiTwo p (Path.Homotopic.Quotient.mk q) =
      Quotient.mk' (loopUncurry ((genLoopEquivOfUnique (Fin 1)).symm (cappedLoop p q))) := rfl

section Naturality
variable {Y : Type v} [TopologicalSpace Y] {y : Y} (f : C(X, Y)) (h : f x = y)

/-- The cancellation cap is preserved pointwise by every pointed continuous map. -/
theorem cancellationPath_natural (p : Path x x) (s t : unitInterval) :
    basedLoopMap f h (cancellationPath p s) t =
      cancellationPath (basedLoopMap f h p) s t := rfl

/-- Right translation of based loops is preserved pointwise by every pointed map. -/
theorem rightTranslate_natural (p q : Path x x) :
    basedLoopMap f h (rightTranslate p q) =
      rightTranslate (basedLoopMap f h p) (basedLoopMap f h q) := by
  ext t
  change f ((q.trans p.symm) t) = _
  simp only [rightTranslate, ContinuousMap.coe_mk, Path.trans_apply, basedLoopMap,
    Path.cast_coe, Path.map_coe, Function.comp_apply, Path.symm_apply]
  split_ifs <;> rfl

/-- The entire capped cylinder is natural pointwise, including the added caps. -/
theorem cappedLoop_natural (p : Path x x) (q : Path p p) (s : unitInterval) :
    basedLoopMap f h (cappedLoop p q s) =
      cappedLoop (basedLoopMap f h p) (q.map (basedLoopMap f h).continuous) s := by
  ext t
  simp only [cappedLoop, Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact cancellationPath_natural f h p _ t
  · exact congrArg (fun k : Path y y => k t) (rightTranslate_natural f h p (q _))
  · exact cancellationPath_natural f h p _ t

/-- The canonical conversion of a loop-space cylinder to pi_2 is natural for
every pointed continuous map, with the genuine homotopy group map. -/
theorem loopComponentToPiTwo_natural (p : Path x x) (a : FundamentalGroup (Path x x) p) :
    piMap 1 f h (loopComponentToPiTwo p a) =
      loopComponentToPiTwo (basedLoopMap f h p)
        (FundamentalGroup.map (basedLoopMap f h) p a) := by
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  rw [componentToPiTwo_eq_cube]
  change Quotient.mk' (genLoopPostcomp f h
    (loopUncurry ((genLoopEquivOfUnique (Fin 1)).symm (cappedLoop p q)))) = _
  rw [show FundamentalGroup.map (basedLoopMap f h) p (Path.Homotopic.Quotient.mk q) =
    Path.Homotopic.Quotient.mk (q.map (basedLoopMap f h).continuous) from rfl,
    componentToPiTwo_eq_cube]
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro z
  exact congrArg (fun k : Path y y => k (z 0)) (cappedLoop_natural f h p q (z 1))

end Naturality
end Quillen.Automorphism.Cap

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Automorphism
open scoped ZeroObject

namespace Quillen.Automorphism.Diagram
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)
  (A : C)

lemma qObj_ne_zero (hA : A ≠ 0) : Q.of EC.deflation EC.inflation A ≠ EC.qZero := by
  intro h
  exact hA (congrArg (fun X : EC.QCategory => X.obj.of) h)

lemma normalizedQ_zero : F.normalizedQ.obj EC.qZero = ED.qZero :=
  rebaseFunctor_obj_base _ _ _ _

lemma normalizedQ_obj (hA : A ≠ 0) :
    F.normalizedQ.obj (Q.of EC.deflation EC.inflation A) =
      Q.of ED.deflation ED.inflation (F.toFunctor.obj A) := by
  classical
  simp only [_root_.CategoryTheory.ExactCategory.ExactFunctor.normalizedQ, rebaseFunctor, rebaseObj,
    ite_eq_right (qObj_ne_zero (EC := EC) A hA)]
  rfl

/-- Under the actual zero normalization used by KMap, the zero-apex arm is
literally the target zero-apex arm, with only equality transports remaining. -/
theorem normalizedQ_zeroArm (hA : A ≠ 0) :
    eqToHom (normalizedQ_zero F).symm ≫
      F.normalizedQ.map (EC.fromZero (Q.of EC.deflation EC.inflation A)) ≫
        eqToHom (normalizedQ_obj F A hA) =
      ED.fromZero (Q.of ED.deflation ED.inflation (F.toFunctor.obj A)) := by
  classical
  simp only [ExactFunctor.normalizedQ, rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [mapQ_zeroCone]
  simp

/-- The full-apex arm has the identical normalization law. -/
theorem normalizedQ_fullArm (hA : A ≠ 0) :
    eqToHom (normalizedQ_zero F).symm ≫
      F.normalizedQ.map (fullFromZero EC A) ≫
        eqToHom (normalizedQ_obj F A hA) =
      fullFromZero ED (F.toFunctor.obj A) := by
  classical
  simp only [ExactFunctor.normalizedQ, rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [mapQ_fullCone]
  simp

/-- The middle automorphism is the actual image automorphism, with the same
object transport as the two arms. -/
theorem normalizedQ_automorphism (hA : A ≠ 0) (α : Aut A) :
    eqToHom (normalizedQ_obj F A hA).symm ≫
      F.normalizedQ.map (EC.qIsoOfIso α).hom ≫ eqToHom (normalizedQ_obj F A hA) =
      (ED.qIsoOfIso (F.toFunctor.mapIso α)).hom := by
  classical
  simp only [ExactFunctor.normalizedQ, rebaseFunctor, rebaseObjIso,
    dite_eq_right (qObj_ne_zero (EC := EC) A hA), eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact congrArg Iso.hom (F.mapQ_qIsoOfIso α)

/-- The omitted zero-object case of automorphism-class naturality is automatic. -/
theorem automorphismClass_of_isZero (E : ExactStructure C) (A : C) (hZ : IsZero A)
    (α : Aut A) : automorphismClass E A α = 1 := by
  have hα : α = 1 := Iso.ext (hZ.eq_of_src α.hom (𝟙 A))
  rw [hα, map_one]

end Quillen.Automorphism.Diagram


end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Automorphism
  Quillen.Automorphism.Diagram Quillen.Automorphism.Cap
open scoped ZeroObject Topology unitInterval

namespace Quillen.Automorphism.Functoriality

section HomotopyCongruence
variable {B D : Type u} [SmallCategory B] [SmallCategory D]
  {F G F' G' : B ⥤ D}

/-- Equality transports on the endpoint functors do not change their realized cylinder. -/
theorem realizedTransformation_congr (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G')
    (hα : α ≫ eqToHom hG = eqToHom hF ≫ β)
    (t : unitInterval) (x : ClassifyingSpace B) :
    classifyingSpaceNaturalTransformationHomotopy α (t,x) =
      classifyingSpaceNaturalTransformationHomotopy β (t,x) := by
  subst F'
  subst G'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hα
  subst β
  rfl
end HomotopyCongruence

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]

/-- A universe-compatible one-object category with the original automorphisms as arrows. -/
def AutIndex (_A : C) : Type u := ULift.{u} Unit

instance (A : C) : SmallCategory (AutIndex A) where
  Hom _ _ := Aut A
  id _ := 1
  comp f g := g * f
  id_comp _ := mul_one _
  comp_id _ := one_mul _
  assoc f g h := (mul_assoc h g f).symm

/-- The unique object of the displayed automorphism-index category. -/
def autVertex (A : C) : AutIndex A := ULift.up ()

/-- The original automorphism action as a functor into the core. -/
def autCore (A : C) : AutIndex A ⥤ Core C where
  obj _ := Core.mk A
  map α := CoreHom.mk α
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual Q row indexed by automorphisms of the given object. -/
abbrev autRow (E : ExactStructure C) (A : C) : AutIndex A ⥤ E.QCategory :=
  autCore A ⋙ coreQ E

/-- The zero-apex cone restricted to the displayed automorphism row. -/
abbrev autZeroCone (E : ExactStructure C) (A : C) := Functor.whiskerLeft (autCore A) (zeroCone E)
/-- The full-apex cone restricted to the displayed automorphism row. -/
abbrev autFullCone (E : ExactStructure C) (A : C) := Functor.whiskerLeft (autCore A) (fullCone E)

section ExactFunctor
variable {D : Type u} [SmallCategory D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED) (A : C)

/-- An exact functor carries the actual automorphism-index category to its image. -/
def autIndexMap : AutIndex A ⥤ AutIndex (F.toFunctor.obj A) where
  obj _ := autVertex _
  map α := F.toFunctor.mapIso α
  map_id _ := F.toFunctor.mapIso_refl _
  map_comp α β := (F.toFunctor.mapAut A).map_mul β α

lemma normalizedAutConst_eq :
    (autCore A ⋙ (Functor.const (Core C)).obj EC.qZero) ⋙ F.normalizedQ =
      autIndexMap F A ⋙ (autCore (F.toFunctor.obj A) ⋙ (Functor.const (Core D)).obj ED.qZero) := by
  refine CategoryTheory.Functor.ext (fun _ => normalizedQ_zero F) ?_
  intro X Y α
  simp

lemma normalizedAutRow_eq (hA : A ≠ 0) :
    autRow EC A ⋙ F.normalizedQ =
      autIndexMap F A ⋙ autRow ED (F.toFunctor.obj A) := by
  refine CategoryTheory.Functor.ext (fun _ => normalizedQ_obj F A hA) ?_
  intro X Y α
  apply (cancel_epi (eqToHom (normalizedQ_obj F A hA).symm)).mp
  apply (cancel_mono (eqToHom (normalizedQ_obj F A hA))).mp
  simpa only [Functor.comp_map, autCore, coreQ, autIndexMap, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using
      normalizedQ_automorphism F A hA α

lemma normalizedAutZeroCone_eq (hA : A ≠ 0) :
    Functor.whiskerRight (autZeroCone EC A) F.normalizedQ ≫
        eqToHom (normalizedAutRow_eq F A hA) =
      eqToHom (normalizedAutConst_eq F A) ≫
        Functor.whiskerLeft (autIndexMap F A) (autZeroCone ED (F.toFunctor.obj A)) := by
  apply NatTrans.ext
  funext X
  apply (cancel_epi (eqToHom (normalizedQ_zero F).symm)).mp
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, autZeroCone, zeroCone, autCore, coreQ, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using normalizedQ_zeroArm F A hA

lemma normalizedAutFullCone_eq (hA : A ≠ 0) :
    Functor.whiskerRight (autFullCone EC A) F.normalizedQ ≫
        eqToHom (normalizedAutRow_eq F A hA) =
      eqToHom (normalizedAutConst_eq F A) ≫
        Functor.whiskerLeft (autIndexMap F A) (autFullCone ED (F.toFunctor.obj A)) := by
  apply NatTrans.ext
  funext X
  apply (cancel_epi (eqToHom (normalizedQ_zero F).symm)).mp
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, autFullCone, fullCone, autCore, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using normalizedQ_fullArm F A hA

lemma zeroCone_realized_natural (hA : A ≠ 0)
    (t : unitInterval) (x : ClassifyingSpace (AutIndex A)) :
    classifyingSpaceMap F.normalizedQ
      (classifyingSpaceNaturalTransformationHomotopy (zeroCone EC)
        (t, classifyingSpaceMap (autCore A) x)) =
      classifyingSpaceNaturalTransformationHomotopy (zeroCone ED)
        (t, classifyingSpaceMap (autCore (F.toFunctor.obj A))
          (classifyingSpaceMap (autIndexMap F A) x)) := by
  have H := realizedTransformation_congr (normalizedAutConst_eq F A) (normalizedAutRow_eq F A hA)
    (Functor.whiskerRight (autZeroCone EC A) F.normalizedQ)
    (Functor.whiskerLeft (autIndexMap F A) (autZeroCone ED (F.toFunctor.obj A)))
    (normalizedAutZeroCone_eq F A hA) t x
  simpa only [classifyingSpaceNaturalTransformationHomotopy_whiskerRight,
    autZeroCone, classifyingSpaceNaturalTransformationHomotopy_whiskerLeft] using H

lemma fullCone_realized_natural (hA : A ≠ 0)
    (t : unitInterval) (x : ClassifyingSpace (AutIndex A)) :
    classifyingSpaceMap F.normalizedQ
      (classifyingSpaceNaturalTransformationHomotopy (fullCone EC)
        (t, classifyingSpaceMap (autCore A) x)) =
      classifyingSpaceNaturalTransformationHomotopy (fullCone ED)
        (t, classifyingSpaceMap (autCore (F.toFunctor.obj A))
          (classifyingSpaceMap (autIndexMap F A) x)) := by
  have H := realizedTransformation_congr (normalizedAutConst_eq F A) (normalizedAutRow_eq F A hA)
    (Functor.whiskerRight (autFullCone EC A) F.normalizedQ)
    (Functor.whiskerLeft (autIndexMap F A) (autFullCone ED (F.toFunctor.obj A)))
    (normalizedAutFullCone_eq F A hA) t x
  simpa only [classifyingSpaceNaturalTransformationHomotopy_whiskerRight,
    autFullCone, classifyingSpaceNaturalTransformationHomotopy_whiskerLeft] using H

/-- Naturality of the entire loop-valued map on the one-object automorphism diagram. -/
theorem autLoopMap_natural (hA : A ≠ 0) (x : ClassifyingSpace (AutIndex A)) :
    basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point
      (coreLoopMap EC (classifyingSpaceMap (autCore A) x)) =
    coreLoopMap ED (classifyingSpaceMap (autCore (F.toFunctor.obj A))
      (classifyingSpaceMap (autIndexMap F A) x)) := by
  ext t
  change classifyingSpaceMap F.normalizedQ
    (((conePath EC (zeroCone EC) _).trans (conePath EC (fullCone EC) _).symm) t) =
      ((conePath ED (zeroCone ED) _).trans (conePath ED (fullCone ED) _).symm) t
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact zeroCone_realized_natural F A hA _ x
  · exact fullCone_realized_natural F A hA _ x

/-- The base loop in this naturality square is the actual target object loop. -/
theorem objectLoop_natural (hA : A ≠ 0) :
    basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point
      (coreLoopMap EC (classifyingSpacePoint (Core.mk A))) =
    coreLoopMap ED (classifyingSpacePoint (Core.mk (F.toFunctor.obj A))) := by
  simpa only [classifyingSpaceMap_point, autCore, autIndexMap] using
    autLoopMap_natural F A hA (classifyingSpacePoint (autVertex A))

/-- The original realized automorphism cylinder commutes pointwise with normalizedQ. -/
theorem automorphismCylinder_natural (hA : A ≠ 0) (α : Aut A) (s : unitInterval) :
    basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point
      (automorphismCylinder EC α s) =
    automorphismCylinder ED (F.toFunctor.mapIso α) s := by
  have H := autLoopMap_natural F A hA
    (classifyingSpacePath (C := AutIndex A) (c := autVertex A) (d := autVertex A) α s)
  simpa only [classifyingSpacePath_naturality, autCore, autIndexMap,
    automorphismCylinder, Path.map_coe, Function.comp_apply] using H

end ExactFunctor
section ClassNaturality
variable {X : Type*} [TopologicalSpace X] {x : X}

lemma componentToPiTwo_congr {p p' : Path x x} (hp : p = p')
    (q : Path p p) (q' : Path p' p') (hq : ∀ t, q t = q' t) :
    loopComponentToPiTwo p (Path.Homotopic.Quotient.mk q) =
      loopComponentToPiTwo p' (Path.Homotopic.Quotient.mk q') := by
  subst p'
  have hq' : q = q' := Path.ext (funext hq)
  subst q'
  rfl
end ClassNaturality

/-- Exact functors preserve the actual canonical automorphism class. -/
theorem automorphismClass_natural
    {D : Type u} [SmallCategory D] [Preadditive D] [HasFiniteBiproducts D]
    {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)
    (A : C) (α : Aut A) :
    F.KMap 1 (automorphismClass EC A α) =
      automorphismClass ED (F.toFunctor.obj A) (F.toFunctor.mapIso α) := by
  classical
  by_cases hA : A = 0
  · have hZ : IsZero A := hA ▸ isZero_zero C
    have hα : α = 1 := Iso.ext (hZ.eq_of_src α.hom (𝟙 A))
    rw [hα, map_one, map_one]
    have he : F.toFunctor.mapIso (1 : Aut A) = (1 : Aut (F.toFunctor.obj A)) :=
      F.toFunctor.mapIso_refl A
    rw [he, map_one]
  · rw [automorphismClass_eq, automorphismClass_eq]
    refine (loopComponentToPiTwo_natural
      (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point
      (coreLoopMap EC (classifyingSpacePoint (Core.mk A)))
      (Path.Homotopic.Quotient.mk (automorphismCylinder EC α))).trans ?_
    change loopComponentToPiTwo _
      (Path.Homotopic.Quotient.mk ((automorphismCylinder EC α).map
        (basedLoopMap (classifyingSpaceMap F.normalizedQ).hom
          F.normalizedQ_map_point).continuous)) = _
    apply componentToPiTwo_congr (objectLoop_natural F A hA)
    exact automorphismCylinder_natural F A hA α

end Quillen.Automorphism.Functoriality


end
