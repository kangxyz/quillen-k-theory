/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence

/-!
# Actual global units and complete small-model reference isomorphisms

The original geometric unit retains its chosen-zero normalization and genuine small-model
lift. Actual pullback preserves the forward pulled-back scalar, independently of the
centrality of an identity action along a full reference isomorphism. These equations do
not identify dependent carrier nodes, merge source casts, or construct a mixed cone filler.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.FunctorIdentityAutomorphism
universe u u₁ v₁
namespace Quillen.PerfectComplexes.GlobalUnitReferenceNaturality

attribute [local irreducible] boundedFlatPerfectGlobalUnitIso

local instance {X : Scheme.{u}} :
    (AsSmall.down : SmallModel (BoundedFlatPerfect X) ⥤ BoundedFlatPerfect X).IsEquivalence :=
  (AsSmall.equiv : BoundedFlatPerfect X ≌
    SmallModel (BoundedFlatPerfect X)).isEquivalence_inverse

/-- The original chosen-zero conjugation is the same actual target identity action. -/
theorem normalizedUnit_eq_onFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPullbackNormalizationIso f).symm ≪≫
      boundedFlatPerfectPullbackUnitIso f r ≪≫ boundedFlatPullbackNormalizationIso f =
    onFunctor (boundedFlatNormalizedPullback f) (boundedFlatPerfectGlobalUnitIso X r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := (boundedFlatPerfectGlobalUnitIso X r).hom.naturality
    ((boundedFlatPullbackNormalizationIso f).hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    boundedFlatPerfectPullbackUnitIso, rightUnitor_inv_app, rightUnitor_hom_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Category.id_comp, onFunctor_hom_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-- Actual normalized pullback preserves the original forward pulled-back scalar. -/
theorem normalizedPullback_preserves {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) :
    Preserves (boundedFlatNormalizedPullback f) (boundedFlatPerfectGlobalUnitIso Y r)
      (boundedFlatPerfectGlobalUnitIso X (Units.map f.appTop.hom.toMonoidHom r)) :=
  map_hom_eq_of_iso (boundedFlatNormalizedPullback f) (boundedFlatPerfectPullback f)
    (boundedFlatPullbackNormalizationIso f).symm _ _
    (boundedFlatPerfectPullback_map_globalUnit f r)

/-- Faithful lowering identifies the entire original up/down lift with its small identity action. -/
theorem small_onFunctor {R : CommRingCat.{u}} {i k : Index R}
    (F : BoundedFlatPerfect (space i) ⥤ BoundedFlatPerfect (space k))
    (r : (Γ(space k, ⊤))ˣ) :
    isoWhiskerLeft AsSmall.down
      (isoWhiskerRight (onFunctor F (boundedFlatPerfectGlobalUnitIso (space k) r))
        AsSmall.up) =
    onFunctor (AsSmall.down ⋙ F ⋙ AsSmall.up) (boundedFlatCoefficientSmallUnitIso k r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (AsSmall.down : SmallModel (BoundedFlatPerfect (space k)) ⥤
    BoundedFlatPerfect (space k)).map_injective
  change AsSmall.down.{u, u + 1, 0}.map
      (AsSmall.up.{u, u + 1, 0}.map
        ((onFunctor F (boundedFlatPerfectGlobalUnitIso (space k) r)).hom.app
          (ULift.down K))) =
    AsSmall.down.{u, u + 1, 0}.map
      ((boundedFlatCoefficientSmallUnitIso k r).hom.app
        (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K))))
  calc
    _ = (boundedFlatPerfectGlobalUnitIso (space k) r).hom.app
        (F.obj (ULift.down K)) := by
      simp only [AsSmall.down_map, AsSmall.up_map_down, onFunctor_hom_app]
    _ = _ := (map_lift_hom
      (AsSmall.down.{u, u + 1, 0} : SmallModel (BoundedFlatPerfect (space k)) ⥤
        BoundedFlatPerfect (space k))
      (boundedFlatPerfectGlobalUnitIso (space k) r)
      (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K)))).symm

/-- The original unit, normalization and small-model transport give the full action iso. -/
theorem normalizedModelUnit_eq_onFunctor {R : CommRingCat.{u}} {i k : Index R}
    (f : space k ⟶ space i) (r : (Γ(space k, ⊤))ˣ) :
    isoWhiskerLeft AsSmall.down (isoWhiskerRight
      ((boundedFlatPullbackNormalizationIso f).symm ≪≫
        boundedFlatPerfectPullbackUnitIso f r ≪≫ boundedFlatPullbackNormalizationIso f)
      AsSmall.up) =
    onFunctor (AsSmall.down ⋙ boundedFlatNormalizedPullback f ⋙ AsSmall.up)
      (boundedFlatCoefficientSmallUnitIso k r) := by
  rw [normalizedUnit_eq_onFunctor]
  exact small_onFunctor (boundedFlatNormalizedPullback f) r

/-- The same small-model pullback preserves the forward unit, using genuine scalar pullback. -/
theorem normalizedModel_preserves {R : CommRingCat.{u}} {i k : Index R}
    (f : space k ⟶ space i) (r : (Γ(space i, ⊤))ˣ) :
    Preserves (AsSmall.down ⋙ boundedFlatNormalizedPullback f ⋙ AsSmall.up)
      (boundedFlatCoefficientSmallUnitIso i r)
      (boundedFlatCoefficientSmallUnitIso k (Units.map f.appTop.hom.toMonoidHom r)) := by
  intro K
  apply (AsSmall.down : SmallModel (BoundedFlatPerfect (space k)) ⥤
    BoundedFlatPerfect (space k)).map_injective
  change (boundedFlatNormalizedPullback f).map
      (AsSmall.down.map ((boundedFlatCoefficientSmallUnitIso i r).hom.app K)) =
    AsSmall.down.map
      ((boundedFlatCoefficientSmallUnitIso k
        (Units.map f.appTop.hom.toMonoidHom r)).hom.app
          (AsSmall.up.obj ((boundedFlatNormalizedPullback f).obj (AsSmall.down.obj K))))
  rw [boundedFlatCoefficientSmallUnitIso, map_lift_hom,
    boundedFlatCoefficientSmallUnitIso, map_lift_hom]
  exact normalizedPullback_preserves f r (AsSmall.down.obj K)

/-- The actual small target unit intertwines along any complete reference isomorphism. -/
theorem reference_intertwine {R : CommRingCat.{u}} (k : Index R)
    (r : (Γ(space k, ⊤))ˣ) {C : Type u₁} [Category.{v₁} C]
    (F G : C ⥤ SmallModel (BoundedFlatPerfect (space k))) (ρ : F ≅ G) :
    onFunctor F (boundedFlatCoefficientSmallUnitIso k r) ≪≫ ρ =
      ρ ≪≫ onFunctor G (boundedFlatCoefficientSmallUnitIso k r) := by
  have h := onFunctor_intertwine F G (𝟭 (SmallModel (BoundedFlatPerfect (space k))))
    (ρ.hom ≫ (Functor.rightUnitor G).inv)
    (boundedFlatCoefficientSmallUnitIso k r) (boundedFlatCoefficientSmallUnitIso k r)
    (fun _ ↦ rfl)
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.trans_hom, NatTrans.comp_app, rightUnitor_inv_app,
    whiskerRight_app, Functor.id_map, Category.comp_id] using NatTrans.congr_app h K

end Quillen.PerfectComplexes.GlobalUnitReferenceNaturality
