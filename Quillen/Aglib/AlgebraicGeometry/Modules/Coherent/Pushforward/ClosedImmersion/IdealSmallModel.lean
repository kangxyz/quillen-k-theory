/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealFiltration
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Aglib.CategoryTheory.SmallModel.Exact

/-!
# Small models of the annihilated coherent image

The actual closed pushforward is an exact categorical equivalence onto the annihilated objects in
the genuine supported small model. The source and target universes and canonical factorizations are
preserved.-/
@[expose] public section

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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (openMap R I)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap R I)

local instance : PreservesFiniteColimits (coherentRestrictionExact (openMap R I)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap R I)

local instance : (coherentRestrictionExact (openMap R I)).toFunctor.IsLocalization
    (coherentRestrictionExact (openMap R I)).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap R I)

/-- The canonical upper-universe small model of actual closed pushforward. -/
abbrev smallPushforward :=
  (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1} (coherentPushforwardExact R
    I)).toFunctor

/-- The represented actual pushforward is killed by I, including the
canonical small-model unit isomorphism. -/
theorem smallPushforward_killed
    (M : SmallModel.{u + 1} (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R I)))) :
    finiteTypeSheavesKilledBy R I ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse.obj
      ((smallPushforward R I).obj M)) :=
  (finiteTypeSheavesKilledBy R I).prop_of_iso
    ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).unitIso.app
      ((coherentPushforward R I).obj
        ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
          (Pushforward.ClosedImmersion.Ideal.closedRing R I)))).inverse.obj M)))
    (coherentPushforward_killed R I _)

/-- Actual closed pushforward, landing in the actual small support category. -/
def smallPushforwardToSupport :
    SmallModel.{u+1} (FiniteTypeSheaves (Spec (Pushforward.ClosedImmersion.Ideal.closedRing R
      I))) ⥤ SmallSupport R I :=
  ObjectProperty.lift _ (smallPushforward R I) (fun M ↦ by
    rw [coherentGlobalSmallSupport_iff]
    exact finiteTypeSheavesKilledBy_le_supportedAway R I _ (smallPushforward_killed R I M))

/-- Its precise smaller target consists of the actual killed supported objects. -/
def smallPushforwardToKilled :
    SmallModel.{u+1} (FiniteTypeSheaves (Spec (Pushforward.ClosedImmersion.Ideal.closedRing R I))) ⥤
      (supportKilled R I).FullSubcategory :=
  ObjectProperty.lift _ (smallPushforwardToSupport R I) (fun M ↦
    (supportKilled_iff R I _).mpr (smallPushforward_killed R I M))

instance smallPushforward_full : (smallPushforward R I).Full := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
    (Pushforward.ClosedImmersion.Ideal.closedRing R I)))).inverse ⋙
    coherentPushforward R I) ⋙ (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).functor).Full
  infer_instance

instance smallPushforward_faithful : (smallPushforward R I).Faithful := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
    (Pushforward.ClosedImmersion.Ideal.closedRing R I)))).inverse ⋙
    coherentPushforward R I) ⋙
      (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).functor).Faithful
  infer_instance

instance smallPushforwardToKilled_full : (smallPushforwardToKilled R I).Full where
  map_surjective {M N} a := by
    obtain ⟨b, hb⟩ := (smallPushforward R I).map_surjective a.hom.hom
    exact ⟨b, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hb)⟩

instance smallPushforwardToKilled_faithful : (smallPushforwardToKilled R I).Faithful where
  map_injective h := (smallPushforward R I).map_injective
    (congrArg (fun a ↦ a.hom.hom) h)

/-- Every annihilated supported object comes from an actual coherent sheaf
on the affine closed subscheme. -/
instance smallPushforwardToKilled_essSurj : (smallPushforwardToKilled R I).EssSurj where
  mem_essImage M := by
    let N : (finiteTypeSheavesKilledBy R I).FullSubcategory :=
      ⟨(equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse.obj M.obj.obj,
        (supportKilled_iff R I M.obj).mp M.property⟩
    let L := (coherentClosedEquivalence R I).inverse.obj N
    let e : (coherentPushforward R I).obj L ≅ N.obj :=
      (finiteTypeSheavesKilledBy R I).ι.mapIso ((coherentClosedEquivalence R I).counitIso.app N)
    let Q := equivSmallModel.{u+1} (FiniteTypeSheaves (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R I)))
    let A := equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact A.functor.mapIso
      ((coherentPushforward R I).mapIso (Q.unitIso.app L).symm ≪≫ e) ≪≫
        A.counitIso.app M.obj.obj

instance smallPushforwardToKilled_isEquivalence :
    (smallPushforwardToKilled R I).IsEquivalence := {}

instance smallPushforwardToKilled_additive : (smallPushforwardToKilled R I).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (smallPushforward R I).map_add

/-- Actual small closed pushforward with the original transported source
exact structure, rather than a newly chosen unrelated K-map. -/
def smallPushforwardToKilledExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Spec (Pushforward.ClosedImmersion.Ideal.closedRing R I))))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled R I)) where
  toFunctor := smallPushforwardToKilled R I
  map_conflation S h := by
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R I))))).conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance smallPushforwardToKilledExact_isEquivalence :
    (smallPushforwardToKilledExact R I).toFunctor.IsEquivalence :=
  smallPushforwardToKilled_isEquivalence R I

/-- The canonical factorization of actual closed pushforward through support. -/
def smallPushforwardToSupportExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Spec (Pushforward.ClosedImmersion.Ideal.closedRing R I))))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (coherentGlobalSmallSupport (openMap
        R I))) :=
  (smallPushforwardToKilledExact R I).comp (CategoryTheory.ObjectProperty.exactInclusion
    (supportKilled R I))

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
