/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationUnit

/-! # Genuine tensor multiplication through the actual Model comparison

The scalar identification is proved from the actual tensor unitor square and naturality.
Both selected-zero conjugations remain in the Model transformation used by realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The unitor identifies the actual tensor multiplication with the same objectwise scalar. -/
theorem tensorAutomorphism_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (K : BoundedFlatPerfect Y) :
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K =
      (boundedFlatPerfectGlobalUnitIso X r).hom.app
        ((boundedFlatPerfectTensorUnitPullback f).obj K) := by
  have hp : (boundedFlatPerfectPullbackUnitIso f r).hom.app K =
      (boundedFlatPerfectGlobalUnitIso X r).hom.app
        ((boundedFlatPerfectPullback f).obj K) := by
    simp only [boundedFlatPerfectPullbackUnitIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    exact Category.comp_id _
  apply (cancel_mono ((boundedFlatPerfectTensorUnitPullbackIso f).hom.app K)).mp
  have h := NatTrans.congr_app
    (boundedFlatPerfectTensorUnitPullbackAutomorphism_unitor f r) K
  simp only [NatTrans.comp_app] at h
  rw [h, hp]
  exact (boundedFlatPerfectGlobalUnitIso X r).hom.naturality
    ((boundedFlatPerfectTensorUnitPullbackIso f).hom.app K)

local instance {X : Scheme.{u}} :
    (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect X) ⥤
      BoundedFlatPerfect X).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect X ≌
    Quillen.Waldhausen.SmallModel (BoundedFlatPerfect X)).isEquivalence_inverse

/-- The fixed raw rebase retains the original genuine tensor automorphism. -/
theorem tensorModelTransformation_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackModelTransformation f r =
      (onFunctor (tensorUnitPullbackModelMap f).functor
        (evaluationSmallUnit (op X) r)).hom := by
  apply NatTrans.ext
  funext K
  change Quillen.Waldhausen.SmallModel (BoundedFlatPerfect Y) at K
  apply (AsSmall.down : Quillen.Waldhausen.SmallModel (BoundedFlatPerfect X) ⥤
    BoundedFlatPerfect X).map_injective
  rw [onFunctor_hom_app, evaluationSmallUnit, map_lift_hom]
  simp only [tensorUnitPullbackModelTransformation, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  rw [tensorAutomorphism_scalar]
  let p := boundedFlatPerfectTensorUnitPullback f
  let h := boundedFlatPerfectTensorUnitPullback_exact f
  let q := Quillen.rebaseFunctor p
    (boundedFlatPerfectWaldhausen Y).zero (boundedFlatPerfectWaldhausen X).zero
    ((h.zero (boundedFlatPerfectWaldhausen Y).isZero).iso
      (boundedFlatPerfectWaldhausen X).isZero)
  let z : p ≅ q := Quillen.rebaseFunctorIso _ _ _ _
  have hn := (boundedFlatPerfectGlobalUnitIso X r).hom.naturality
    (z.hom.app (AsSmall.down.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj K) ≫
      (boundedFlatPerfectGlobalUnitIso X r).hom.app (p.obj (AsSmall.down.obj K)) ≫
      z.hom.app (AsSmall.down.obj K) =
    (boundedFlatPerfectGlobalUnitIso X r).hom.app (q.obj (AsSmall.down.obj K))
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-- The complete Model comparison intertwines the original internal and tensor units. -/
theorem internalTensorModelIso_unit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    whiskerRight
      (onFunctor (globalModel.map (coefficientMap Q X).op).functor
        (globalUnit (op (scheme Q (laurent.op.obj X)))
          (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
      (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor ≫
      (internalTensorModelIso Q X).hom =
    (internalTensorModelIso Q X).hom ≫
      whiskerLeft (evaluationModel (op (scheme Q X))).functor
        (tensorUnitPullbackModelTransformation (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)) := by
  rw [tensorModelTransformation_scalar]
  exact onFunctor_whisker_square (globalModel.map (coefficientMap Q X).op).functor
    (tensorUnitPullbackModelMap (coefficientMap Q X)).functor
    (evaluationModel (op (scheme Q X))).functor
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor
    (internalTensorModelIso Q X).hom
    (globalUnit (op (scheme Q (laurent.op.obj X)))
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (evaluationSmallUnit (op (scheme Q (laurent.op.obj X)))
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (evaluationModel_unit (op (scheme Q (laurent.op.obj X)))
      (ParameterLaurentUnit.projectedLaurentScalar Q X)).whisker

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
