/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Principal
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.PrincipalFiltration
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Aglib.CategoryTheory.SmallModel.Exact

/-!
# Small models of the annihilated coherent image

The actual closed pushforward is an exact categorical equivalence onto the annihilated objects in
the genuine supported small model. The source and target universes and canonical factorizations are
preserved.-/
@[expose] public section

open AlgebraicGeometry.Scheme

open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

open Quillen

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (principalOpen R f)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (principalOpen R f)

local instance : PreservesFiniteColimits (coherentRestrictionExact (principalOpen R f)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (principalOpen R f)

local instance : (coherentRestrictionExact (principalOpen R f)).toFunctor.IsLocalization
    (coherentRestrictionExact (principalOpen R f)).toFunctor.kernel.isoModSerre :=
  coherentPrincipalRestriction_isLocalization_kernel R f

/-- The canonical upper-universe small model of actual closed pushforward. -/
abbrev smallPushforward :=
  (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1}
    (Modules.Coherent.Pushforward.ClosedImmersion.Ideal.coherentPushforwardExact R (Ideal.span
    {f}))).toFunctor

/-- The represented actual pushforward is killed by f, including the
canonical small-model unit isomorphism. -/
theorem smallPushforward_killed
    (M : SmallModel.{u + 1} (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))))) :
    finiteTypeSheavesKilledBy R f ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse.obj
      ((smallPushforward R f).obj M)) :=
  (finiteTypeSheavesKilledBy R f).prop_of_iso
    ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).unitIso.app
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
        (Pushforward.ClosedImmersion.Ideal.closedMap R
        (Ideal.span {f}))).obj
        ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
          (Pushforward.ClosedImmersion.Ideal.closedRing R
          (Ideal.span {f}))))).inverse.obj M)))
    (coherentPushforward_killed R f _)

/-- Actual closed pushforward, landing in the actual small support category. -/
def smallPushforwardToSupport :
    SmallModel.{u+1} (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f})))) ⥤ SmallSupport R f :=
  ObjectProperty.lift _ (smallPushforward R f) (fun M ↦ by
    rw [AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSmallSupport_iff,
      finiteTypeSheavesSupportedAway_iff_uniform]
    refine ⟨1, ?_⟩
    intro m
    simpa only [pow_one] using smallPushforward_killed R f M m)

/-- Its precise smaller target consists of the actual killed supported objects. -/
def smallPushforwardToKilled :
    SmallModel.{u+1} (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f})))) ⥤
      (supportKilled R f).FullSubcategory :=
  ObjectProperty.lift _ (smallPushforwardToSupport R f) (fun M ↦
    (supportKilled_iff R f _).mpr (smallPushforward_killed R f M))

instance smallPushforward_full : (smallPushforward R f).Full := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
    (Pushforward.ClosedImmersion.Ideal.closedRing R
    (Ideal.span {f}))))).inverse ⋙
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (Pushforward.ClosedImmersion.Ideal.closedMap R
      (Ideal.span {f}))) ⋙ (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).functor).Full
  infer_instance

instance smallPushforward_faithful : (smallPushforward R f).Faithful := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
    (Pushforward.ClosedImmersion.Ideal.closedRing R
    (Ideal.span {f}))))).inverse ⋙
    AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (Pushforward.ClosedImmersion.Ideal.closedMap R
      (Ideal.span {f}))) ⋙
      (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).functor).Faithful
  infer_instance

instance smallPushforwardToKilled_full : (smallPushforwardToKilled R f).Full where
  map_surjective {M N} a := by
    obtain ⟨b, hb⟩ := (smallPushforward R f).map_surjective a.hom.hom
    exact ⟨b, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hb)⟩

instance smallPushforwardToKilled_faithful : (smallPushforwardToKilled R f).Faithful where
  map_injective h := (smallPushforward R f).map_injective
    (congrArg (fun a ↦ a.hom.hom) h)

/-- Every annihilated supported object comes from an actual coherent sheaf
on the principal closed subscheme. -/
instance smallPushforwardToKilled_essSurj : (smallPushforwardToKilled R f).EssSurj where
  mem_essImage M := by
    let N : (finiteTypeSheavesKilledBy R f).FullSubcategory :=
      ⟨(equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse.obj M.obj.obj,
        (supportKilled_iff R f M.obj).mp M.property⟩
    let L := (coherentClosedEquivalence R f).inverse.obj N
    let e : (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (Pushforward.ClosedImmersion.Ideal.closedMap R
      (Ideal.span {f}))).obj L ≅ N.obj :=
      (finiteTypeSheavesKilledBy R f).ι.mapIso ((coherentClosedEquivalence R f).counitIso.app N)
    let Q := equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))))
    let A := equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact A.functor.mapIso
      ((AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward
        (Pushforward.ClosedImmersion.Ideal.closedMap R
        (Ideal.span {f}))).mapIso (Q.unitIso.app L).symm ≪≫ e) ≪≫
        A.counitIso.app M.obj.obj

instance smallPushforwardToKilled_isEquivalence :
    (smallPushforwardToKilled R f).IsEquivalence := {}

instance smallPushforwardToKilled_additive : (smallPushforwardToKilled R f).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (smallPushforward R f).map_add

/-- Actual small closed pushforward with the original transported source
exact structure, rather than a newly chosen unrelated K-map. -/
def smallPushforwardToKilledExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f})))))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled R f)) where
  toFunctor := smallPushforwardToKilled R f
  map_conflation S h := by
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1} (abelianExactStructure
      (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f})))))).conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance smallPushforwardToKilledExact_isEquivalence :
    (smallPushforwardToKilledExact R f).toFunctor.IsEquivalence :=
  smallPushforwardToKilled_isEquivalence R f

/-- The canonical factorization of actual closed pushforward through support. -/
def smallPushforwardToSupportExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f})))))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure
        (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSmallSupport (principalOpen R f)))
        :=
  (smallPushforwardToKilledExact R f).comp (CategoryTheory.ObjectProperty.exactInclusion
    (supportKilled R f))

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
