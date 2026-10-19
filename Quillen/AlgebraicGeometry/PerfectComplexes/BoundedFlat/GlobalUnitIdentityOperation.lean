/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitKOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductSwapUnit
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIdentityAction
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationLevelExt

/-!
# Original geometric unit operations as genuine target identity actions

The complete chosen-zero normalization and small-model lift of the original
projection-unit track are retained. Its K-operation is the target scalar
identity action after the original geometric pullback, in every nonnegative
degree. The same identity action is natural under arbitrary scheme pullback.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalUnitIdentityOperation

attribute [local irreducible] boundedFlatPerfectGlobalUnitIso

private instance smallDownIsEquivalence {X : Scheme.{u}} :
    (AsSmall.down : SmallModel (BoundedFlatPerfect X) ⥤ BoundedFlatPerfect X).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect X ≌
    SmallModel (BoundedFlatPerfect X)).isEquivalence_inverse

/-- The original scalar action on the original K-group of its own scheme. -/
def unitKOperation (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    BoundedFlatPerfectK X n →* BoundedFlatPerfectK X (n + 1) :=
  originalKSelfTrackOperation (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectWaldhausen X)
    (prespectrumIsoHomotopy (𝟙 (modelOf (boundedFlatPerfectWaldhausen X)))
      (ProductSwapUnit.smallUnit X r)) n

/-- Faithful lowering retains the entire lifted scalar identity action. -/
theorem small_onFunctor {X Y : Scheme.{u}}
    (F : BoundedFlatPerfect Y ⥤ BoundedFlatPerfect X) (r : (Γ(X, ⊤))ˣ) :
    isoWhiskerLeft AsSmall.down
      (isoWhiskerRight (onFunctor F (boundedFlatPerfectGlobalUnitIso X r)) AsSmall.up) =
    onFunctor (AsSmall.down ⋙ F ⋙ AsSmall.up) (ProductSwapUnit.smallUnit X r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (AsSmall.down : SmallModel (BoundedFlatPerfect X) ⥤
    BoundedFlatPerfect X).map_injective
  change AsSmall.down.{u, u + 1, 0}.map
      (AsSmall.up.{u, u + 1, 0}.map
        ((onFunctor F (boundedFlatPerfectGlobalUnitIso X r)).hom.app (ULift.down K))) =
    AsSmall.down.{u, u + 1, 0}.map
      ((ProductSwapUnit.smallUnit X r).hom.app
        (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K))))
  calc
    _ = (boundedFlatPerfectGlobalUnitIso X r).hom.app (F.obj (ULift.down K)) := by
      simp only [AsSmall.down_map, AsSmall.up_map_down, onFunctor_hom_app]
    _ = _ := (map_lift_hom
      (AsSmall.down.{u, u + 1, 0} : SmallModel (BoundedFlatPerfect X) ⥤
        BoundedFlatPerfect X)
      (boundedFlatPerfectGlobalUnitIso X r)
      (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K)))).symm

/-- The original normalized geometric unit is precisely the target small identity action. -/
theorem normalizedModelUnit_eq_onFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    isoWhiskerLeft AsSmall.down (isoWhiskerRight
      ((boundedFlatPullbackNormalizationIso f).symm ≪≫
        boundedFlatPerfectPullbackUnitIso f r ≪≫ boundedFlatPullbackNormalizationIso f)
      AsSmall.up) =
    onFunctor (AsSmall.down ⋙ boundedFlatNormalizedPullback f ⋙ AsSmall.up)
      (ProductSwapUnit.smallUnit X r) := by
  rw [GlobalUnitReferenceNaturality.normalizedUnit_eq_onFunctor]
  exact small_onFunctor (boundedFlatNormalizedPullback f) r

/-- Every original time and spectrum level retains the same target scalar action. -/
theorem originalUnit_level {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (boundedFlatPerfectUnitHomotopy f r).level n =
      ((prespectrumIsoHomotopy (𝟙 (modelOf (boundedFlatPerfectWaldhausen X)))
        (ProductSwapUnit.smallUnit X r)).precomp (boundedFlatPerfectPrespectrumMap f)).level n := by
  let M := modelMap (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectWaldhausen X)
    (boundedFlatNormalizedPullback_exact f) (boundedFlatNormalizedPullback_obj_zero f)
  change (prespectrumIsoHomotopy M (isoWhiskerLeft AsSmall.down (isoWhiskerRight
      ((boundedFlatPullbackNormalizationIso f).symm ≪≫
        boundedFlatPerfectPullbackUnitIso f r ≪≫ boundedFlatPullbackNormalizationIso f)
      AsSmall.up))).level n = _
  rw [normalizedModelUnit_eq_onFunctor]
  exact prespectrumIsoHomotopy_onFunctor_level M (ProductSwapUnit.smallUnit X r) n

/-- The original geometric unit operation factors through its actual pullback K-map. -/
theorem originalUnit_operation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Y)
      (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy f r) n =
      (unitKOperation X r n).comp (boundedFlatPerfectKPullback f n) := by
  rw [originalKSelfTrackOperation_eq_of_levels (boundedFlatPerfectWaldhausen Y)
    (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy f r)
    ((prespectrumIsoHomotopy (𝟙 (modelOf (boundedFlatPerfectWaldhausen X)))
      (ProductSwapUnit.smallUnit X r)).precomp (boundedFlatPerfectPrespectrumMap f))
    (originalUnit_level f r)]
  exact originalKSelfTrackOperation_precomp (boundedFlatPerfectWaldhausen X)
    (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectWaldhausen Y) _
    (boundedFlatPerfectPullback_exact f) n

/-- At the identity projection the original operation is the same target identity action. -/
theorem originalIdentityUnit_operation (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (boundedFlatPerfectWaldhausen X)
      (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy (𝟙 X) r) n =
      unitKOperation X r n := by
  rw [originalUnit_operation, boundedFlatPerfectKPullback_id, MonoidHom.comp_id]

/-- Arbitrary actual pullback preserves the original scalar identity operation. -/
theorem unitKOperation_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) (n : ℕ) :
    (boundedFlatPerfectKPullback f (n + 1)).comp (unitKOperation Y r n) =
      (unitKOperation X (Units.map f.appTop.hom.toMonoidHom r) n).comp
        (boundedFlatPerfectKPullback f n) := by
  rw [← originalIdentityUnit_operation,
    boundedFlatPerfectUnitHomotopy_originalKOperation_postcomp, Category.comp_id,
    originalUnit_operation]

end Quillen.PerfectComplexes.GlobalUnitIdentityOperation
