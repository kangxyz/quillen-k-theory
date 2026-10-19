/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationNaturality

/-! # Original unit transport through the actual global evaluation comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalEvaluation boundedFlatPerfectGlobalUnitIso

local instance {X : Scheme.{u}} :
    (AsSmall.down : SmallModel (BoundedFlatPerfect X) ⥤
      BoundedFlatPerfect X).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect X ≌ SmallModel (BoundedFlatPerfect X)).isEquivalence_inverse

/-- The unchanged original raw geometric unit, with its actual zero normalization and lift. -/
def evaluationRawUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (evaluationRawMap f).functor ⟶
      (evaluationRawMap f).functor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation
      (boundedFlatPerfectPullback_exact f)
      (boundedFlatPerfectPullback_exact f)
      (boundedFlatPerfectPullbackUnitIso
        f r).hom) AsSmall.up)

/-- Its forward component is exactly the same target unit on the actual normalized raw functor. -/
theorem evaluationRawUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    evaluationRawUnit f r =
      (onFunctor (evaluationRawMap f).functor
        (evaluationSmallUnit (Opposite.op X) r)).hom := by
  apply NatTrans.ext
  funext K
  change Quillen.Waldhausen.SmallModel (BoundedFlatPerfect Y) at K
  apply (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect X) ⥤
    BoundedFlatPerfect X).map_injective
  rw [onFunctor_hom_app, evaluationSmallUnit, map_lift_hom]
  simp only [evaluationRawUnit, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  let p := boundedFlatPerfectPullback f
  let h := boundedFlatPerfectPullback_exact f
  let q := Quillen.rebaseFunctor p
    (boundedFlatPerfectWaldhausen Y).zero
    (boundedFlatPerfectWaldhausen X).zero
    ((h.zero (boundedFlatPerfectWaldhausen Y).isZero).iso
      (boundedFlatPerfectWaldhausen X).isZero)
  let z : p ≅ q := Quillen.rebaseFunctorIso _ _ _ _
  simp only [boundedFlatPerfectPullbackUnitIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom]
  have hn := (boundedFlatPerfectGlobalUnitIso X r).hom.naturality
    (z.hom.app (AsSmall.down.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj K) ≫
      (boundedFlatPerfectGlobalUnitIso X r).hom.app
        (p.obj (AsSmall.down.obj K)) ≫ z.hom.app (AsSmall.down.obj K) =
    (boundedFlatPerfectGlobalUnitIso X r).hom.app (q.obj (AsSmall.down.obj K))
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-- The full actual evaluation comparison intertwines both original normalized units. -/
theorem evaluation_unit_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    whiskerRight (onFunctor (globalModel.map f.op).functor
        (globalUnit (Opposite.op X) r)).hom (evaluationModel (Opposite.op X)).functor ≫
      (evaluationComparisonIso f).hom =
    (evaluationComparisonIso f).hom ≫
      whiskerLeft (evaluationModel (Opposite.op Y)).functor (evaluationRawUnit f r) := by
  rw [evaluationRawUnit_eq]
  exact onFunctor_whisker_square (globalModel.map f.op).functor
    (evaluationRawMap f).functor (evaluationModel (Opposite.op Y)).functor
    (evaluationModel (Opposite.op X)).functor (evaluationComparisonIso f).hom
    (globalUnit (Opposite.op X) r) (evaluationSmallUnit (Opposite.op X) r)
    (evaluationModel_unit (Opposite.op X) r).whisker

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
