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
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Filtration
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Aglib.CategoryTheory.SmallModel.Exact

/-!
# Small models of the annihilated coherent image

The actual closed pushforward is an exact categorical equivalence onto the annihilated objects in the genuine supported small model. The source and target universes and canonical factorizations are preserved.
-/
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

local instance : PreservesFiniteLimits (coherentRestrictionExact (openMap i)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap i)

local instance : PreservesFiniteColimits (coherentRestrictionExact (openMap i)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap i)

local instance : (coherentRestrictionExact (openMap i)).toFunctor.IsLocalization
    (coherentRestrictionExact (openMap i)).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap i)

/-- The genuine closed pushforward equivalence onto its annihilated image. -/

def coherentClosedEquivalence : FiniteTypeSheaves Z ≌ (coherentKilled i).FullSubcategory :=
  (coherentPushforward i).toEssImage.asEquivalence

/-- The canonical upper-universe small model of actual closed pushforward. -/

abbrev smallPushforward :=
  (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1} (coherentPushforwardExact
    i)).toFunctor

/-- The represented actual pushforward is killed by the closed ideal, including the
canonical small-model unit isomorphism. -/

theorem smallPushforward_killed
    (M : SmallModel.{u + 1} (FiniteTypeSheaves Z)) :
    coherentKilled i ((equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse.obj
      ((smallPushforward i).obj M)) :=
  (coherentKilled i).prop_of_iso
    ((equivSmallModel.{u+1} (FiniteTypeSheaves X)).unitIso.app
      ((coherentPushforward i).obj
        ((equivSmallModel.{u+1} (FiniteTypeSheaves Z)).inverse.obj M)))
    ((coherentPushforward i).obj_mem_essImage _)

/-- Actual closed pushforward, landing in the actual small support category. -/

def smallPushforwardToSupport :
    SmallModel.{u+1} (FiniteTypeSheaves Z) ⥤ SmallSupport i :=
  ObjectProperty.lift _ (smallPushforward i) (fun M ↦ by
    rw [coherentGlobalSmallSupport_iff]
    exact coherentKilled_le_supported i _ (smallPushforward_killed i M))

/-- Its precise smaller target consists of the actual killed supported objects. -/

def smallPushforwardToKilled :
    SmallModel.{u+1} (FiniteTypeSheaves Z) ⥤
      (supportKilled i).FullSubcategory :=
  ObjectProperty.lift _ (smallPushforwardToSupport i) (fun M ↦
    smallPushforward_killed i M)

instance smallPushforward_full : (smallPushforward i).Full := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves Z)).inverse ⋙
    coherentPushforward i) ⋙ (equivSmallModel.{u+1} (FiniteTypeSheaves X)).functor).Full
  infer_instance

instance smallPushforward_faithful : (smallPushforward i).Faithful := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves Z)).inverse ⋙
    coherentPushforward i) ⋙ (equivSmallModel.{u+1} (FiniteTypeSheaves X)).functor).Faithful
  infer_instance

instance smallPushforwardToKilled_full : (smallPushforwardToKilled i).Full where
  map_surjective {M N} a := by
    obtain ⟨b, hb⟩ := (smallPushforward i).map_surjective a.hom.hom
    exact ⟨b, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hb)⟩

instance smallPushforwardToKilled_faithful : (smallPushforwardToKilled i).Faithful where
  map_injective h := (smallPushforward i).map_injective
    (congrArg (fun a ↦ a.hom.hom) h)

/-- Every annihilated supported object comes from an actual coherent sheaf
on the closed subscheme. -/

instance smallPushforwardToKilled_essSurj : (smallPushforwardToKilled i).EssSurj where
  mem_essImage M := by
    let N : (coherentKilled i).FullSubcategory :=
      ⟨(equivSmallModel.{u+1} (FiniteTypeSheaves X)).inverse.obj M.obj.obj,
        M.property⟩
    let L := (coherentClosedEquivalence i).inverse.obj N
    let e : (coherentPushforward i).obj L ≅ N.obj :=
      (coherentKilled i).ι.mapIso ((coherentClosedEquivalence i).counitIso.app N)
    let Q := equivSmallModel.{u+1} (FiniteTypeSheaves Z)
    let A := equivSmallModel.{u+1} (FiniteTypeSheaves X)
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact A.functor.mapIso
      ((coherentPushforward i).mapIso (Q.unitIso.app L).symm ≪≫ e) ≪≫
        A.counitIso.app M.obj.obj

instance smallPushforwardToKilled_isEquivalence :
    (smallPushforwardToKilled i).IsEquivalence := {}

instance smallPushforwardToKilled_additive : (smallPushforwardToKilled i).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (smallPushforward i).map_add

/-- Actual small closed pushforward with the original transported source
exact structure, rather than a newly chosen unrelated K-map. -/

def smallPushforwardToKilledExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Z)))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled i)) where
  toFunctor := smallPushforwardToKilled i
  map_conflation S h := by
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves Z))).conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance smallPushforwardToKilledExact_isEquivalence :
    (smallPushforwardToKilledExact i).toFunctor.IsEquivalence :=
  smallPushforwardToKilled_isEquivalence i

/-- The canonical factorization of actual closed pushforward through support. -/

def smallPushforwardToSupportExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Z)))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (coherentGlobalSmallSupport (openMap
        i))) :=
  (smallPushforwardToKilledExact i).comp (CategoryTheory.ObjectProperty.exactInclusion
    (supportKilled i))

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
