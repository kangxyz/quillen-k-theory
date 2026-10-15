/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralSupportDevissage

/-!
# Geometric closed-support dévissage

Actual closed sheaf pushforward factors through the annihilated objects in
the compatible small supported category. It is an exact equivalence only
onto those annihilated objects. Genuine ideal-kernel dévissage then gives
the supported G-equivalence, with the original canonical pushforward map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.General
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
      (Devissage.subcategoryExactStructure (supportKilled i)) where
  toFunctor := smallPushforwardToKilled i
  map_conflation S h := by
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves Z))).conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance smallPushforwardToKilledExact_isEquivalence :
    (smallPushforwardToKilledExact i).toFunctor.IsEquivalence :=
  smallPushforwardToKilled_isEquivalence i

instance smallPushforwardToKilledExact_mapQ_isEquivalence :
    (smallPushforwardToKilledExact i).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves Z))).inflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    have : Mono ((smallPushforwardToKilled i).map a) :=
      (abelianExactStructure_inflation_iff _ _).mp ha
    exact Functor.mono_of_mono_map (smallPushforwardToKilled i) this
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves Z))).deflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    have : Epi ((smallPushforwardToKilled i).map a) :=
      (abelianExactStructure_deflation_iff _ _).mp ha
    exact Functor.epi_of_epi_map (smallPushforwardToKilled i) this

/-- Public scheme G-theory of the closed subscheme is equivalent
to the actual compatible supported G-term by geometric dévissage. -/
def closedSupportGEquiv (n : ℕ) :
    CoherentScheme.G Z n ≃* CoherentGlobalSupportedG (openMap i) n :=
  ((smallPushforwardToKilledExact i).KEquivOfMapQIsEquivalence n).trans
    (supportDevissageKEquiv i n)

/-- The canonical factorization of actual closed pushforward through support. -/
def smallPushforwardToSupportExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Z)))
      (Devissage.subcategoryExactStructure (coherentGlobalSmallSupport (openMap i))) :=
  (smallPushforwardToKilledExact i).comp (Devissage.exactInclusion (supportKilled i))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    (↑(closedSupportGEquiv i n) :
      CoherentScheme.G Z n →* CoherentGlobalSupportedG (openMap i) n) =
      (smallPushforwardToSupportExact i).KMap n := by
  rw [smallPushforwardToSupportExact, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

/-- The geometric dévissage comparison preserves exactly the canonical G-map
of actual sheaf pushforward, including small-model and zero normalizations. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (openMap i)) n).comp
        (closedSupportGEquiv i n).toMonoidHom = coherentPushforwardGMap i n := by
  have h : ((smallPushforwardToKilledExact i).comp
      (Devissage.exactInclusion (supportKilled i))).comp
      (Devissage.exactInclusion (coherentGlobalSmallSupport (openMap i))) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1} (coherentPushforwardExact i)).comp
      (SmallModelLocalization.standardExactFunctor.{u+1} (FiniteTypeSheaves X)) := by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [CategoryTheory.ExactCategory.ExactFunctor.KMap_comp] at hk
  ext x
  apply (SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).injective
  change SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n
      ((SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves X) n).symm
        (Devissage.KMap (coherentGlobalSmallSupport (openMap i)) n
          (Devissage.KMap (supportKilled i) n
            ((smallPushforwardToKilledExact i).KMap n x)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

end Quillen.CoherentScheme.ClosedImmersion.General
