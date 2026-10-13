/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.AffinePullback
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralPushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.GluingLocality
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Actual coherent pullback along closed immersions

Affine pullback is ordinary extension of scalars. The genuine pullback on
module sheaves respects open restriction and therefore preserves coherence
by the actual affine open cover of the target and its pullback cover.
The resulting coherent adjunction is the restriction of the sheaf adjunction.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.General
open Scheme.Modules

/-- Coherent sheaves pull back along a closed immersion into an affine
scheme, using its actual quotient-ring presentation. -/
theorem affineLocallyFiniteType_pullback_affine {Z : Scheme.{u}} (R : CommRingCat.{u})
    (i : Z ⟶ Spec R) [IsClosedImmersion i] {M : (Spec R).Modules}
    (hM : affineLocallyFiniteType (Spec R) M) :
    affineLocallyFiniteType Z ((Scheme.Modules.pullback i).obj M) := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  have hq : affineLocallyFiniteType (Spec (Ideal.closedRing R I))
      ((Scheme.Modules.pullback (Ideal.closedMap R I)).obj M) :=
    (affineLocallyFiniteType_spec_iff _ _).mpr
      (affineFiniteSheaf_pullback (CommRingCat.ofHom (Ideal.Quotient.mk I))
        ((affineLocallyFiniteType_spec_iff R M).mp hM))
  have he : affineLocallyFiniteType Z
      ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback (Ideal.closedMap R I)).obj M)) :=
    (affineLocallyFiniteType Z).prop_of_iso ((restrictFunctorIsoPullback e.hom).app _)
      (affineLocallyFiniteType_restrict e.hom hq)
  exact (affineLocallyFiniteType Z).prop_of_iso
    (((pullbackComp e.hom (Ideal.closedMap R I)) ≪≫ (pullbackCongr hi).symm).app M) he

/-- Coherence is detected on any actual scheme open cover. -/
theorem affineLocallyFiniteType_of_schemeOpenCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (𝒰 : Scheme.OpenCover.{u} X)
    (hM : ∀ j, affineLocallyFiniteType (𝒰.X j) ((restrictFunctor (𝒰.f j)).obj M)) :
      affineLocallyFiniteType X M := by
  have h (j : 𝒰.I₀) : (M.restrict (𝒰.f j).opensRange.ι).IsFinitePresentation := by
    let e : restrictFunctor (𝒰.f j) ⋙ restrictFunctor (𝒰.f j).isoOpensRange.inv ≅
        restrictFunctor (𝒰.f j).opensRange.ι :=
      (restrictFunctorComp (𝒰.f j).isoOpensRange.inv (𝒰.f j)).symm ≪≫
        restrictFunctorCongr (𝒰.f j).isoOpensRange_inv_comp
    exact affineLocallyFiniteType_finitePresentation
      ((affineLocallyFiniteType (𝒰.f j).opensRange.toScheme).prop_of_iso (e.app M)
        (affineLocallyFiniteType_restrict (𝒰.f j).isoOpensRange.inv (hM j)))
  have : M.IsFinitePresentation :=
    finitePresentation_of_openCover M (fun j ↦ (𝒰.f j).opensRange)
      𝒰.isOpenCover_opensRange h
  exact affineLocallyFiniteType_of_finitePresentation M

/-- Actual pullback along a closed immersion preserves coherence on a
locally noetherian source, by actual open-cover descent. -/
theorem affineLocallyFiniteType_pullback {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] {M : X.Modules} (hM : affineLocallyFiniteType X M) :
    affineLocallyFiniteType Z ((Scheme.Modules.pullback i).obj M) := by
  let 𝒰 := X.affineOpenCover.openCover.pullback₁ i
  apply affineLocallyFiniteType_of_schemeOpenCover _ 𝒰
  intro j
  let a := X.affineOpenCover.f j
  have h : affineLocallyFiniteType (pullback i a)
      ((Scheme.Modules.pullback (pullback.snd i a)).obj ((restrictFunctor a).obj M)) :=
    affineLocallyFiniteType_pullback_affine (X.affineOpenCover.X j) (pullback.snd i a)
      (affineLocallyFiniteType_restrict a hM)
  exact (affineLocallyFiniteType (pullback i a)).prop_of_iso
    ((Quillen.SchemeSheaf.pullbackOpenSquare (pullback.fst i a) (pullback.snd i a) i a
      (pullback.condition (f := i) (g := a))).app M).symm h

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual module-sheaf pullback restricted to coherent objects. -/
def coherentPullback : FiniteTypeSheaves X ⥤ FiniteTypeSheaves Z :=
  ObjectProperty.lift _ (finiteTypeSheavesToModules X ⋙ Scheme.Modules.pullback i)
    (fun M ↦ affineLocallyFiniteType_pullback i M.property)

omit [IsLocallyNoetherian X] in
/-- Forgetting coherence yields precisely the actual sheaf pullback. -/
theorem coherentPullback_comp_inclusion :
    coherentPullback i ⋙ finiteTypeSheavesToModules Z =
      finiteTypeSheavesToModules X ⋙ Scheme.Modules.pullback i := rfl

/-- Actual pullback and open restriction commute on coherent objects. -/
def coherentPullbackOpenBaseChange {V : Scheme.{u}}
    (a : V ⟶ X) [IsOpenImmersion a] :
    coherentPullback i ⋙ finiteTypeSheavesRestriction (pullback.fst i a) ≅
      finiteTypeSheavesRestriction a ⋙ coherentPullback (pullback.snd i a) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules (pullback i a))
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X)
      (Quillen.SchemeSheaf.pullbackOpenSquare (pullback.fst i a) (pullback.snd i a) i a
        (pullback.condition (f := i) (g := a))))

/-- The coherent adjunction is the restriction of the genuine sheaf
pullback–pushforward adjunction. -/
def coherentAdjunction : coherentPullback i ⊣ coherentPushforward i :=
  (pullbackPushforwardAdjunction i).restrictFullyFaithful
    (affineLocallyFiniteType X).fullyFaithfulι (affineLocallyFiniteType Z).fullyFaithfulι (Iso.refl
      _) (Iso.refl _)

instance coherentPullback_isLeftAdjoint : (coherentPullback i).IsLeftAdjoint :=
  (coherentAdjunction i).isLeftAdjoint

instance coherentPushforward_isRightAdjoint : (coherentPushforward i).IsRightAdjoint :=
  (coherentAdjunction i).isRightAdjoint

instance coherentPullback_additive : (coherentPullback i).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.pullback i).map_add

omit [IsLocallyNoetherian X] in
/-- The coherent unit has the actual underlying sheaf-adjunction unit. -/
@[simp] theorem coherentAdjunction_unit_hom (M : FiniteTypeSheaves X) :
    ((coherentAdjunction i).unit.app M).hom = (pullbackPushforwardAdjunction i).unit.app M.obj := by
  change (finiteTypeSheavesToModules X).map ((coherentAdjunction i).unit.app M) = _
  dsimp only [coherentAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  change (pullbackPushforwardAdjunction i).unit.app M.obj ≫
      (pushforward i).map (𝟙 ((Scheme.Modules.pullback i).obj M.obj)) ≫ 𝟙 _ = _
  simp only [CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id]
  exact CategoryTheory.Category.comp_id _

omit [IsLocallyNoetherian X] in
/-- The coherent counit has the actual underlying sheaf-adjunction counit. -/
@[simp] theorem coherentAdjunction_counit_hom (M : FiniteTypeSheaves Z) :
    ((coherentAdjunction i).counit.app M).hom =
      (pullbackPushforwardAdjunction i).counit.app M.obj := by
  change (finiteTypeSheavesToModules Z).map ((coherentAdjunction i).counit.app M) = _
  dsimp only [coherentAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  change 𝟙 _ ≫ (Scheme.Modules.pullback i).map (𝟙 ((pushforward i).obj M.obj)) ≫
      (pullbackPushforwardAdjunction i).counit.app M.obj = _
  simp only [CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp]

end Quillen.CoherentScheme.ClosedImmersion.General
