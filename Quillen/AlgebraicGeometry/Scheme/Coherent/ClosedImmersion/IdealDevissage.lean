/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealSupportDevissage

/-!
# Geometric affine closed-support dévissage

Actual closed sheaf pushforward factors through the annihilated objects in
the compatible small supported category. It is an exact equivalence only
onto those annihilated objects. Genuine finite-image dévissage then gives
the supported G-equivalence, with the original canonical pushforward map.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

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
    (M : SmallModel.{u + 1} (FiniteTypeSheaves (Spec (closedRing R I)))) :
    finiteTypeSheavesKilledBy R I ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse.obj
      ((smallPushforward R I).obj M)) :=
  (finiteTypeSheavesKilledBy R I).prop_of_iso
    ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).unitIso.app
      ((coherentPushforward R I).obj
        ((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec (closedRing R I)))).inverse.obj M)))
    (coherentPushforward_killed R I _)

/-- Actual closed pushforward, landing in the actual small support category. -/
def smallPushforwardToSupport :
    SmallModel.{u+1} (FiniteTypeSheaves (Spec (closedRing R I))) ⥤ SmallSupport R I :=
  ObjectProperty.lift _ (smallPushforward R I) (fun M ↦ by
    rw [coherentGlobalSmallSupport_iff]
    exact finiteTypeSheavesKilledBy_le_supportedAway R I _ (smallPushforward_killed R I M))

/-- Its precise smaller target consists of the actual killed supported objects. -/
def smallPushforwardToKilled :
    SmallModel.{u+1} (FiniteTypeSheaves (Spec (closedRing R I))) ⥤
      (supportKilled R I).FullSubcategory :=
  ObjectProperty.lift _ (smallPushforwardToSupport R I) (fun M ↦
    (supportKilled_iff R I _).mpr (smallPushforward_killed R I M))

instance smallPushforward_full : (smallPushforward R I).Full := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec (closedRing R I)))).inverse ⋙
    coherentPushforward R I) ⋙ (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).functor).Full
  infer_instance

instance smallPushforward_faithful : (smallPushforward R I).Faithful := by
  change (((equivSmallModel.{u+1} (FiniteTypeSheaves (Spec (closedRing R I)))).inverse ⋙
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
    let Q := equivSmallModel.{u+1} (FiniteTypeSheaves (Spec (closedRing R I)))
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
      (coherentExactStructure (Spec (closedRing R I))))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled R I)) where
  toFunctor := smallPushforwardToKilled R I
  map_conflation S h := by
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves (Spec (closedRing R I))))).conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance smallPushforwardToKilledExact_isEquivalence :
    (smallPushforwardToKilledExact R I).toFunctor.IsEquivalence :=
  smallPushforwardToKilled_isEquivalence R I

instance smallPushforwardToKilledExact_mapQ_isEquivalence :
    (smallPushforwardToKilledExact R I).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves (Spec (closedRing R I))))).inflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    have : Mono ((smallPushforwardToKilled R I).map a) :=
      (abelianExactStructure_inflation_iff _ _).mp ha
    exact Functor.mono_of_mono_map (smallPushforwardToKilled R I) this
  · intro M N a ha
    change (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (abelianExactStructure (FiniteTypeSheaves (Spec (closedRing R I))))).deflation a
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    have : Epi ((smallPushforwardToKilled R I).map a) :=
      (abelianExactStructure_deflation_iff _ _).mp ha
    exact Functor.epi_of_epi_map (smallPushforwardToKilled R I) this

/-- Public scheme G-theory of the affine closed subscheme is equivalent
to the actual compatible supported G-term by geometric dévissage. -/
def closedSupportGEquiv (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec (closedRing R I)) n ≃*
      CoherentGlobalSupportedG (openMap R I) n :=
  ((smallPushforwardToKilledExact R I).KEquivOfMapQIsEquivalence n).trans
    (supportDevissageKEquiv R I n)

/-- The canonical factorization of actual closed pushforward through support. -/
def smallPushforwardToSupportExact :
    ExactFunctor (CategoryTheory.ExactCategory.ExactStructure.smallModel.{u+1}
      (coherentExactStructure (Spec (closedRing R I))))
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (coherentGlobalSmallSupport (openMap
        R I))) :=
  (smallPushforwardToKilledExact R I).comp (CategoryTheory.ObjectProperty.exactInclusion
    (supportKilled R I))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    (↑(closedSupportGEquiv R I n) :
      AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec (closedRing R I)) n →*
        CoherentGlobalSupportedG (openMap R I) n) =
      (smallPushforwardToSupportExact R I).KMap n := by
  rw [smallPushforwardToSupportExact, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

/-- The geometric dévissage comparison preserves exactly the canonical G-map
of actual sheaf pushforward, including small-model and zero normalizations. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (openMap R I)) n).comp
        (closedSupportGEquiv R I n).toMonoidHom = coherentPushforwardGMap R I n := by
  have h : ((smallPushforwardToKilledExact R I).comp
      (CategoryTheory.ObjectProperty.exactInclusion (supportKilled R I))).comp
      (CategoryTheory.ObjectProperty.exactInclusion (coherentGlobalSmallSupport (openMap R I))) =
    (CategoryTheory.ExactCategory.ExactFunctor.smallModel.{u+1} (coherentPushforwardExact R I)).comp
      (SmallModelLocalization.standardExactFunctor.{u+1} (FiniteTypeSheaves (Spec R))) := by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [CategoryTheory.ExactCategory.ExactFunctor.KMap_comp] at hk
  ext x
  apply (SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves (Spec R)) n).injective
  change SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves (Spec R)) n
      ((SmallModelLocalization.standardKEquiv.{u+1} (FiniteTypeSheaves (Spec R)) n).symm
        (Devissage.KMap (coherentGlobalSmallSupport (openMap R I)) n
          (Devissage.KMap (supportKilled R I) n
            ((smallPushforwardToKilledExact R I).KMap n x)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
