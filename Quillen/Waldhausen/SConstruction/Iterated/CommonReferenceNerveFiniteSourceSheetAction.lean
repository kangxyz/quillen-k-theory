/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteSourceSheetParameters
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation
public import Quillen.Topology.DoubleMappingCylinder.HomotopyDescent

/-!
# The finite source action on the unchanged first sheet

The complete source family acts on the original scalar sheet, including its Laurent baseline,
unchanged cylinder height and original tip. Descent takes values in the continuous-map space of
the finite simplex, so the resulting action is jointly continuous without a global native
evaluation-continuity assertion.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteSourceSheet
open CutOpenCarrier
variable {V W T U : Model.{u}} (D : V ⟶ W) (F : W ⟶ T) (J : T ⟶ U)
variable {k : ℕ} (Z : Fin (k + 1) → Node D)

/-- The Laurent baseline of the target retains its full reference. -/
def targetLaurent : C(|parameterSSet ((D ≫ F) ≫ J)|, target D F J) :=
  (SSet.toTop.map (left₀ (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _))).hom

/-- The target cylinder uses the original height, without any subdivision. -/
def targetCylinder : C(|parameterSSet (D ≫ F)| × I, target D F J) where
  toFun z := DoubleCylinder.realizedCylinder
    (attaching (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)) (erase (D ≫ F))
      (z.1, ULift.up z.2)
  continuous_toFun := (DoubleCylinder.realizedCylinder
    (attaching (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)) (erase (D ≫ F))).hom.continuous.comp
      (by fun_prop)

/-- There is only the original first-sheet tip. -/
def targetTip : target D F J :=
  SSet.toTop.map (right₀ (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _))
    (default : |tipSSet.{u}|)

theorem targetCylinder_zero (y : |parameterSSet (D ≫ F)|) :
    targetCylinder D F J (y, 0) = targetLaurent D F J
      (SSet.toTop.map (attaching (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)) y) := by
  have h := ConcreteCategory.congr_hom
    (DoubleCylinder.realized_isPushout
      (attaching (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)) (erase (D ≫ F))).w (Sum.inl y)
  exact h.trans (FourEdgeTree.SetDescent.eval_realized_left _ _ _).symm

theorem targetCylinder_one (y : |parameterSSet (D ≫ F)|) :
    targetCylinder D F J (y, 1) = targetTip D F J := by
  have h := ConcreteCategory.congr_hom
    (DoubleCylinder.realized_isPushout
      (attaching (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)) (erase (D ≫ F))).w (Sum.inr y)
  exact h.trans ((FourEdgeTree.SetDescent.eval_realized_right _ _ _).symm.trans
    (congrArg (SSet.toTop.map (right₀ (D ≫ F) J ((D ≫ F) ≫ J) (Iso.refl _)))
      (Subsingleton.elim _ _)))

/-- The whole Laurent action, curried only in the compact finite parameter. -/
def laurentFamily : C(|parameterSSet (F ≫ J)|,
    C(StdSimplex ℝ (Fin (k + 1)), target D F J)) :=
  ContinuousMap.curry ((targetLaurent D F J).comp (laurent D F J Z))

/-- The tip does not move with the finite source parameter. -/
def tipFamily : C(|tipSSet.{u}|, C(StdSimplex ℝ (Fin (k + 1)), target D F J)) :=
  ContinuousMap.const _ (ContinuousMap.const _ (targetTip D F J))

/-- The finite source action on the entire original cylinder. -/
def cylinderFamily : C(I × |parameterSSet F|,
    C(StdSimplex ℝ (Fin (k + 1)), target D F J)) :=
  ContinuousMap.curry ⟨fun z ↦
    targetCylinder D F J (polynomial D F Z (z.1.2, z.2), z.1.1), by fun_prop⟩

/-- The exact full attachment equation is the zero face of the descended homotopy. -/
def attachmentHomotopy :
    ((laurentFamily D F J Z).comp
      (SSet.toTop.map (attaching F J (F ≫ J) (Iso.refl _))).hom).Homotopy
    ((tipFamily D F J (k := k)).comp (SSet.toTop.map (erase F)).hom) where
  toContinuousMap := cylinderFamily D F J Z
  map_zero_left y := by
    ext z
    exact (targetCylinder_zero D F J (polynomial D F Z (y, z))).trans
      (congrArg (targetLaurent D F J) (attachment_parameter D F J Z y z)).symm
  map_one_left y := by
    ext z
    exact targetCylinder_one D F J (polynomial D F Z (y, z))

/-- Actual descent on the original first sheet, with values in the finite function space. -/
def curriedAction : C(source F J, C(StdSimplex ℝ (Fin (k + 1)), target D F J)) :=
  DoubleCylinder.homotopyDesc
    (SSet.toTop.map (attaching F J (F ≫ J) (Iso.refl _))) (SSet.toTop.map (erase F))
    (first_isPushout F J (F ≫ J) (Iso.refl _))
    (laurentFamily D F J Z) (tipFamily D F J) (attachmentHomotopy D F J Z)

/-- The continuous finite source action preserves the existing scalar sheet itself. -/
def action : C(source F J × StdSimplex ℝ (Fin (k + 1)), target D F J) :=
  ContinuousMap.uncurry (curriedAction D F J Z)

/-- The whole Laurent baseline has the prescribed full-node product. -/
theorem action_laurent (y : |parameterSSet (F ≫ J)|)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    action D F J Z (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y, z) =
      targetLaurent D F J (laurent D F J Z (y, z)) := by
  have h := ConcreteCategory.congr_hom
    ((first_isPushout F J (F ≫ J) (Iso.refl _)).inr_desc
      (DoubleCylinder.homotopyCylinderMap _ _ _ _ (attachmentHomotopy D F J Z))
      (DoubleCylinder.homotopyEndMap (laurentFamily D F J Z) (tipFamily D F J))
      (DoubleCylinder.homotopyDescent_square _ _ _ _ (attachmentHomotopy D F J Z)))
    (Sum.inl y)
  change curriedAction D F J Z (DoubleCylinder.realizedEnds _ _ (Sum.inl y)) = _ at h
  change curriedAction D F J Z _ z = _
  exact (congrArg (fun y ↦ curriedAction D F J Z y z)
    (FourEdgeTree.SetDescent.eval_realized_left
      (attaching F J (F ≫ J) (Iso.refl _)) (erase F) y)).trans
        (congrArg (fun f ↦ f z) h)

/-- The actual cylinder formula keeps every height and every finite source parameter. -/
theorem action_cylinder (y : |parameterSSet F|) (h : I)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    action D F J Z
      (DoubleCylinder.realizedCylinder (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
        (y, ULift.up h), z) = targetCylinder D F J (polynomial D F Z (y, z), h) := by
  exact congrArg (fun f ↦ f z) (DoubleCylinder.homotopyDesc_apply_cylinder _ _
    (first_isPushout F J (F ≫ J) (Iso.refl _))
    (laurentFamily D F J Z) (tipFamily D F J) (attachmentHomotopy D F J Z) h y)

/-- The original tip is fixed by the entire finite source action. -/
theorem action_tip (y : |tipSSet.{u}|) (z : StdSimplex ℝ (Fin (k + 1))) :
    action D F J Z (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) y, z) =
      targetTip D F J := by
  have h := ConcreteCategory.congr_hom
    ((first_isPushout F J (F ≫ J) (Iso.refl _)).inr_desc
      (DoubleCylinder.homotopyCylinderMap _ _ _ _ (attachmentHomotopy D F J Z))
      (DoubleCylinder.homotopyEndMap (laurentFamily D F J Z) (tipFamily D F J))
      (DoubleCylinder.homotopyDescent_square _ _ _ _ (attachmentHomotopy D F J Z)))
    (Sum.inr y)
  change curriedAction D F J Z (DoubleCylinder.realizedEnds _ _ (Sum.inr y)) = _ at h
  change curriedAction D F J Z _ z = _
  exact (congrArg (fun y ↦ curriedAction D F J Z y z)
    (FourEdgeTree.SetDescent.eval_realized_right
      (attaching F J (F ≫ J) (Iso.refl _)) (erase F) y)).trans
        (congrArg (fun f ↦ f z) h)

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteSourceSheet
