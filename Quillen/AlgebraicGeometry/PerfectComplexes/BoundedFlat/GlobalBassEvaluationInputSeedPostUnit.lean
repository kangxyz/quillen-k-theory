/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedEvaluationCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputUnit
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitReferenceNaturality

/-!
# Original forward-unit anchors under the actual raw Laurent postmap

Actual normalized geometric pullback preserves the pulled-back Laurent scalar. The complete
postcomposition reference therefore intertwines the two original strict evaluated units,
and every full Laurent node keeps its own shifted anchor before realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedPostUnit
open GlobalSectionChangeIndex CommonReferenceNerve

local instance {X : Scheme.{u}} :
    (AsSmall.down : Waldhausen.SmallModel (BoundedFlatPerfect X) ⥤
      BoundedFlatPerfect X).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect X ≌
    Waldhausen.SmallModel (BoundedFlatPerfect X)).isEquivalence_inverse

/-- Actual normalized raw pullback preserves precisely the pulled-back forward scalar. -/
theorem raw_preserves {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(Y, ⊤))ˣ) :
    Preserves (evaluationRawMap f).functor (evaluationSmallUnit (op Y) r)
      (evaluationSmallUnit (op X) (Units.map f.appTop.hom.toMonoidHom r)) := by
  intro K
  change Waldhausen.SmallModel (BoundedFlatPerfect Y) at K
  apply (AsSmall.down : Waldhausen.SmallModel (BoundedFlatPerfect X) ⥤
    BoundedFlatPerfect X).map_injective
  change (boundedFlatNormalizedPullback f).map
      (AsSmall.down.map ((evaluationSmallUnit (op Y) r).hom.app K)) =
    AsSmall.down.map
      ((evaluationSmallUnit (op X) (Units.map f.appTop.hom.toMonoidHom r)).hom.app
        (AsSmall.up.obj ((boundedFlatNormalizedPullback f).obj (AsSmall.down.obj K))))
  rw [evaluationSmallUnit, map_lift_hom, evaluationSmallUnit, map_lift_hom]
  exact GlobalUnitReferenceNaturality.normalizedPullback_preserves f r (AsSmall.down.obj K)

private theorem post_intertwine {V W T : Model.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (R : W ⟶ T) (e : F.functor ≅ (H ≫ R).functor)
    (α : F.functor ≅ F.functor) (δ : H.functor ≅ H.functor)
    (β : 𝟭 W.category ≅ 𝟭 W.category) (γ : 𝟭 T.category ≅ 𝟭 T.category)
    (hα : α = onFunctor F.functor γ) (hδ : δ = onFunctor H.functor β)
    (hR : Preserves R.functor β γ) :
    α ≪≫ e = e ≪≫ isoWhiskerRight δ R.functor := by
  subst α δ
  apply Iso.ext
  exact onFunctor_intertwine F.functor H.functor R.functor e.hom β γ hR

private theorem reanchor_post {V W T : Model.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (R : W ⟶ T) (e : F.functor ≅ (H ≫ R).functor)
    (α : F.functor ≅ F.functor) (δ : H.functor ≅ H.functor)
    (h : α ≪≫ e = e ≪≫ isoWhiskerRight δ R.functor) (N : Node H) :
    CommonReferenceProduct.reanchor α (attachPostcompNode H R F e N) =
      attachPostcompNode H R F e (CommonReferenceProduct.reanchor δ N) := by
  apply congrArg (fun a => (⟨N.1 ≫ R, a⟩ : Node F))
  change α ≪≫ (e ≪≫ isoWhiskerRight N.2 R.functor) =
    e ≪≫ isoWhiskerRight (δ ≪≫ N.2) R.functor
  rw [isoWhiskerRight_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original geometric Laurent scalar equation identifies the exact transported unit. -/
theorem laurent_preserves :
    Preserves (evaluationRawMap (laurent.map g)).functor
      (evaluationSmallUnit (op (laurent.obj Y))
        (GlobalSchemeLaurentTrack.laurentScalar (op Y)))
      (evaluationSmallUnit (op (laurent.obj X))
        (GlobalSchemeLaurentTrack.laurentScalar (op X))) := by
  have h := raw_preserves (laurent.map g) (GlobalSchemeLaurentTrack.laurentScalar (op Y))
  rw [GlobalRawBass.laurentUnit_map] at h
  exact h

/-- The entire existing postcomposition anchor intertwines both actual evaluated strict units. -/
theorem post_unit :
    InputSeedCarrier.commonUnit g ≪≫ InputMixedDesc.postSourceIso g =
      InputMixedDesc.postSourceIso g ≪≫
        isoWhiskerRight (InputSeedEvaluationCarrier.commonUnit Y)
          (evaluationRawMap (laurent.map g)).functor :=
  post_intertwine (InputSeedCarrier.laurentRef g) (InputSeedEvaluationCarrier.laurentRef Y)
    (evaluationRawMap (laurent.map g)) (InputMixedDesc.postSourceIso g)
    (InputSeedCarrier.commonUnit g) (InputSeedEvaluationCarrier.commonUnit Y)
    (evaluationSmallUnit (op (laurent.obj Y)) (GlobalSchemeLaurentTrack.laurentScalar (op Y)))
    (evaluationSmallUnit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X)))
    (InputSeedCarrier.commonUnit_eq_target g) (InputSeedEvaluationCarrier.commonUnit_eq_target Y)
    (laurent_preserves g)

/-- Every original Laurent node retains its complete unit anchor after the actual raw postmap. -/
theorem post_shift (N : Node (InputSeedEvaluationCarrier.laurentRef Y)) :
    CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g) (InputMixedDesc.postNode g N) =
      InputMixedDesc.postNode g
        (CommonReferenceProduct.reanchor (InputSeedEvaluationCarrier.commonUnit Y) N) :=
  reanchor_post (InputSeedCarrier.laurentRef g) (InputSeedEvaluationCarrier.laurentRef Y)
    (evaluationRawMap (laurent.map g)) (InputMixedDesc.postSourceIso g)
    (InputSeedCarrier.commonUnit g) (InputSeedEvaluationCarrier.commonUnit Y) (post_unit g) N

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedPostUnit
