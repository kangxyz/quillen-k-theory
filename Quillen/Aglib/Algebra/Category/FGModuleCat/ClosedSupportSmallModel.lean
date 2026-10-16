/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.Aglib.Algebra.Category.FGModuleCat.PrincipalClosedSupport
public import Quillen.Aglib.Algebra.Category.FGModuleCat.PrincipalSupportSmallModel
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.CentralEndomorphism
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Aglib.CategoryTheory.SmallModel.Exact

/-!
# Small exact models of principal quotient restriction

For a commutative noetherian ring, actual quotient-ring restriction gives an exact equivalence
onto the killed objects of the supported small category, retaining the canonical support
factorization.
-/
@[expose] public section

open CategoryTheory.ExactCategory

open ModuleCat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
open Quillen

namespace Quillen.FiniteModuleLocalization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)

omit [IsNoetherianRing R] in
lemma killedBy_of_iso {M N : FGModuleCat.{u} R} (e : M ≅ N) (hM : killedBy f M) :
    killedBy f N := by
  intro n
  obtain ⟨m, rfl⟩ := (FGModuleCat.isoToLinearEquiv e).surjective n
  rw [← map_smul, hM m, map_zero]

/-- The canonical small-model quotient-ring restriction, with no changed choices. -/
abbrev smallClosedFunctor := (closedRestrictionExact f).smallModel.toFunctor

lemma smallClosedFunctor_killed (M : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) :
    killedBy f ((equivSmallModel (FGModuleCat.{u} R)).inverse.obj
      ((smallClosedFunctor f).obj M)) := by
  apply killedBy_of_iso f
    ((equivSmallModel (FGModuleCat.{u} R)).unitIso.app
      ((closedRestriction f).obj ((equivSmallModel (FGModuleCat.{u} (ClosedRing f))).inverse.obj
        M)))
  exact closedRestriction_killed f _

/-- The actual closed pushforward lands in modules supported on V(f). -/
def smallClosedToSupport : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f)) ⥤ PrincipalSupport f :=
  ObjectProperty.lift _ (smallClosedFunctor f) (fun M ↦ by
    rw [smallTorsion_powers_iff_uniform]
    refine ⟨1, ?_⟩
    intro m
    simpa only [pow_one] using smallClosedFunctor_killed f M m)

/-- Its further factorization lands exactly in the killed-by-f objects. -/
def smallClosedToKilled : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f)) ⥤
    (principalKilled f).FullSubcategory :=
  ObjectProperty.lift _ (smallClosedToSupport f) (fun M ↦
    (principalKilled_iff f _).2 (smallClosedFunctor_killed f M))

instance smallClosedFunctor_full : (smallClosedFunctor f).Full := by
  change (((equivSmallModel (FGModuleCat.{u} (ClosedRing f))).inverse ⋙
    closedRestriction f) ⋙ (equivSmallModel (FGModuleCat.{u} R)).functor).Full
  infer_instance

instance smallClosedFunctor_faithful : (smallClosedFunctor f).Faithful := by
  change (((equivSmallModel (FGModuleCat.{u} (ClosedRing f))).inverse ⋙
    closedRestriction f) ⋙ (equivSmallModel (FGModuleCat.{u} R)).functor).Faithful
  infer_instance

instance smallClosedToKilled_full : (smallClosedToKilled f).Full where
  map_surjective {M N} a := by
    obtain ⟨b, hb⟩ := (smallClosedFunctor f).map_surjective a.hom.hom
    exact ⟨b, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hb)⟩

instance smallClosedToKilled_faithful : (smallClosedToKilled f).Faithful where
  map_injective h := (smallClosedFunctor f).map_injective
    (congrArg (fun a ↦ a.hom.hom) h)

/-- Every killed support object comes from an actual finite quotient-ring module. -/
instance smallClosedToKilled_essSurj : (smallClosedToKilled f).EssSurj where
  mem_essImage M := by
    let N : (killedBy f).FullSubcategory :=
      ⟨(principalRepresentation f).obj M.obj, (principalKilled_iff f M.obj).1 M.property⟩
    let L := (closedEquivalence f).inverse.obj N
    let e : (closedRestriction f).obj L ≅ N.obj :=
      (killedBy f).ι.mapIso ((closedEquivalence f).counitIso.app N)
    let Q := (equivSmallModel (FGModuleCat.{u} (ClosedRing f)))
    let A := (equivSmallModel (FGModuleCat.{u} R))
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact A.functor.mapIso ((closedRestriction f).mapIso (Q.unitIso.app L).symm ≪≫ e) ≪≫
      A.counitIso.app M.obj.obj

instance smallClosedToKilled_isEquivalence : (smallClosedToKilled f).IsEquivalence := {}

instance smallClosedToKilled_additive : (smallClosedToKilled f).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (smallClosedFunctor f).map_add

/-- The actual small restriction functor is an equivalence onto the killed objects. -/
def smallClosedEquivalence : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f)) ≌
    (principalKilled f).FullSubcategory := (smallClosedToKilled f).asEquivalence

/-- This equivalence uses the original transported exact structure on its source. -/
def smallClosedToKilledExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (principalKilled f)) where
  toFunctor := smallClosedToKilled f
  map_conflation S h := by
    rw [show (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) from
      abelianExactStructure_smallModel _] at h
    exact h.map_of_exact _

instance smallClosedToKilledExact_isEquivalence :
    (smallClosedToKilledExact f).toFunctor.IsEquivalence := smallClosedToKilled_isEquivalence f

/-- Actual closed restriction of scalars with codomain in the supported category. -/
def smallClosedToSupportExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel
      (CategoryTheory.ObjectProperty.subcategoryExactStructure (smallTorsion (Submonoid.powers f)))
        :=
  (smallClosedToKilledExact f).comp (CategoryTheory.ObjectProperty.exactInclusion (principalKilled
    f))

end Quillen.FiniteModuleLocalization
