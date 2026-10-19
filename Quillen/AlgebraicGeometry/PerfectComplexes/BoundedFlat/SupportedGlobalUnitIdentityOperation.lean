/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PairPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIdentityAction
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationLevelExt
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationNaturality

/-!
# Original supported scalar identity actions

Actual open-pair pullback preserves the scalar automorphism inside the supported
full subcategory. The entire original chosen-zero-rebased supported scalar track
is the small identity-action track precomposed with that same rebased endpoint.
Its original K-operation is therefore the small identity-action operation, using
the original identity K-map rather than identifying the endpoint maps strictly.
No flatness, cartesian-square, compactness or K-group forget-injectivity premise
is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedGlobalUnitIdentityOperation

attribute [local irreducible] boundedFlatPerfectSupportedGlobalUnitIso

/-- Faithful inclusion retains the actual forward global scalar on supported complexes. -/
theorem unit_hom_original {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : (Γ(X, ⊤))ˣ) (K : (boundedFlatPerfectSupported j).FullSubcategory) :
    (boundedFlatPerfectSupported j).ι.map
        ((boundedFlatPerfectSupportedGlobalUnitIso j r).hom.app K) =
      (complexGlobalUnitIso X r).hom.app K.obj := by
  simp only [boundedFlatPerfectSupportedGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]

/-- Every actual open-pair square preserves the pulled-back scalar within support. -/
theorem pullback_preserves {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (r : (Γ(B.obj.right, ⊤))ˣ) :
    Preserves (boundedFlatPerfectSupportedPullback g)
      (boundedFlatPerfectSupportedGlobalUnitIso B.obj.hom r)
      (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom
        (Units.map g.hom.right.appTop.hom.toMonoidHom r)) := by
  intro K
  apply (boundedFlatPerfectSupported A.obj.hom).ι.map_injective
  change (AlgebraicGeometry.Scheme.Modules.Complex.pullback g.hom.right).map
      ((boundedFlatPerfectSupported B.obj.hom).ι.map
        ((boundedFlatPerfectSupportedGlobalUnitIso B.obj.hom r).hom.app K)) = _
  rw [unit_hom_original, unit_hom_original]
  apply HomologicalComplex.hom_ext
  intro n
  change (Scheme.Modules.pullback g.hom.right).map
      (((complexGlobalUnitIso B.obj.right r).hom.app K.obj).f n) = _
  rw [complexGlobalUnitIso_original_terms, complexGlobalUnitIso_original_terms]
  exact AlgebraicGeometry.Scheme.Modules.pullback_map_globalScalar
    g.hom.right (↑r) (K.obj.X n)

/-- A specified scalar equation gives preservation without changing either original unit. -/
theorem pullback_preserves_of_eq {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (r : (Γ(B.obj.right, ⊤))ˣ) (s : (Γ(A.obj.right, ⊤))ˣ)
    (h : Units.map g.hom.right.appTop.hom.toMonoidHom r = s) :
    Preserves (boundedFlatPerfectSupportedPullback g)
      (boundedFlatPerfectSupportedGlobalUnitIso B.obj.hom r)
      (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom s) := by
  subst s
  exact pullback_preserves g r

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private instance smallDownIsEquivalence {C : Type*} [Category C] :
    (AsSmall.down : SmallModel C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ SmallModel C).isEquivalence_inverse

/-- The supported scalar identity action on the original supported K-group. -/
def unitKOperation (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    BoundedFlatPerfectSupportedK j n →* BoundedFlatPerfectSupportedK j (n + 1) :=
  originalKSelfTrackOperation (boundedFlatPerfectSupportedWaldhausen j)
    (boundedFlatPerfectSupportedWaldhausen j)
    (prespectrumIsoHomotopy (𝟙 (modelOf (boundedFlatPerfectSupportedWaldhausen j)))
      (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r)) n

/-- Faithful lowering preserves the complete lifted supported identity action. -/
theorem small_onFunctor
    (F : (boundedFlatPerfectSupported j).FullSubcategory ⥤
      (boundedFlatPerfectSupported j).FullSubcategory) (r : (Γ(X, ⊤))ˣ) :
    isoWhiskerLeft AsSmall.down
      (isoWhiskerRight (onFunctor F (boundedFlatPerfectSupportedGlobalUnitIso j r)) AsSmall.up) =
    onFunctor (AsSmall.down ⋙ F ⋙ AsSmall.up)
      (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (AsSmall.down : SmallModel (boundedFlatPerfectSupported j).FullSubcategory ⥤
    (boundedFlatPerfectSupported j).FullSubcategory).map_injective
  change AsSmall.down.{u, u + 1, 0}.map
      (AsSmall.up.{u, u + 1, 0}.map
        ((onFunctor F (boundedFlatPerfectSupportedGlobalUnitIso j r)).hom.app (ULift.down K))) =
    AsSmall.down.{u, u + 1, 0}.map
      ((SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r).hom.app
        (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K))))
  calc
    _ = (boundedFlatPerfectSupportedGlobalUnitIso j r).hom.app (F.obj (ULift.down K)) := by
      simp only [AsSmall.down_map, AsSmall.up_map_down, onFunctor_hom_app]
    _ = _ := (map_lift_hom
      (AsSmall.down.{u, u + 1, 0} : SmallModel (boundedFlatPerfectSupported j).FullSubcategory ⥤
        (boundedFlatPerfectSupported j).FullSubcategory)
      (boundedFlatPerfectSupportedGlobalUnitIso j r)
      (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K)))).symm

/-- Conjugating the supported identity action retains its exact rebased target. -/
theorem normalizedUnit_eq_onFunctor (r : (Γ(X, ⊤))ˣ) :
    let W := boundedFlatPerfectSupportedWaldhausen j
    let h := IsExact.id W.cof W.weq
    let i := Quillen.rebaseFunctorIso (𝟭 (boundedFlatPerfectSupported j).FullSubcategory)
      W.zero W.zero ((h.zero W.isZero).iso W.isZero)
    i.symm ≪≫ boundedFlatPerfectSupportedGlobalUnitIso j r ≪≫ i =
      onFunctor _ (boundedFlatPerfectSupportedGlobalUnitIso j r) := by
  dsimp only
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let W := boundedFlatPerfectSupportedWaldhausen j
  let h := IsExact.id W.cof W.weq
  let i := Quillen.rebaseFunctorIso (𝟭 (boundedFlatPerfectSupported j).FullSubcategory)
    W.zero W.zero ((h.zero W.isZero).iso W.isZero)
  have hn := (boundedFlatPerfectSupportedGlobalUnitIso j r).hom.naturality (i.hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at hn
  change i.inv.app K ≫ (boundedFlatPerfectSupportedGlobalUnitIso j r).hom.app K ≫
    i.hom.app K = _
  rw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- Every original time and level retains the canonical rebased identity endpoint. -/
theorem originalUnit_level (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (boundedFlatPerfectSupportedGlobalUnitHomotopy j r).level n =
      ((prespectrumIsoHomotopy (𝟙 (modelOf (boundedFlatPerfectSupportedWaldhausen j)))
        (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r)).precomp
          (boundedFlatPerfectSupportedIdentityPrespectrumMap j)).level n := by
  let W := boundedFlatPerfectSupportedWaldhausen j
  let h := IsExact.id W.cof W.weq
  let i := Quillen.rebaseFunctorIso (𝟭 (boundedFlatPerfectSupported j).FullSubcategory)
    W.zero W.zero ((h.zero W.isZero).iso W.isZero)
  let M := modelMap W W h.rebase (Quillen.rebaseFunctor_obj_base _ _ _ _)
  change (prespectrumIsoHomotopy M (isoWhiskerLeft AsSmall.down
    (isoWhiskerRight (i.symm ≪≫ boundedFlatPerfectSupportedGlobalUnitIso j r ≪≫ i)
      AsSmall.up))).level n = _
  rw [normalizedUnit_eq_onFunctor, small_onFunctor]
  exact prespectrumIsoHomotopy_onFunctor_level M
    (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r) n

/-- The original rebased supported scalar operation equals its small identity action. -/
theorem originalUnit_operation (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (boundedFlatPerfectSupportedWaldhausen j)
      (boundedFlatPerfectSupportedWaldhausen j)
      (boundedFlatPerfectSupportedGlobalUnitHomotopy j r) n = unitKOperation j r n := by
  let W := boundedFlatPerfectSupportedWaldhausen j
  rw [originalKSelfTrackOperation_eq_of_levels W W
    (boundedFlatPerfectSupportedGlobalUnitHomotopy j r)
    ((prespectrumIsoHomotopy (𝟙 (modelOf W))
      (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r)).precomp
      (boundedFlatPerfectSupportedIdentityPrespectrumMap j)) (originalUnit_level j r)]
  change originalKSelfTrackOperation W W
    ((prespectrumIsoHomotopy (𝟙 (modelOf W))
      (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r)).precomp
      (exactOriginalPrespectrumMap W W (IsExact.id _ _))) n = _
  rw [originalKSelfTrackOperation_precomp W W W, KMap_id, MonoidHom.comp_id]
  rfl

end Quillen.PerfectComplexes.SupportedGlobalUnitIdentityOperation
