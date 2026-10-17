/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pullback.ClosedImmersion
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Reflector
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPowerFiltration

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
/-!
# The actual closed reflector on an affine ambient scheme

The quotient presentation identifies the essential image of genuine closed
pushforward with ideal-annihilated coherent sheaves. This concerns the
annihilated objects, rather than all sheaves with the same closed support.
-/
@[expose] public section

open ModuleCat.FiniteLocalization.IdealClosedSupport

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.FiniteModuleLocalization.IdealClosedSupport

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)

instance killedBy_quotients : (killedBy I).IsClosedUnderQuotients where
  prop_of_epi {M N} f hf hM := by
    have : Epi f.hom := inferInstanceAs
      (Epi ((forget₂ (FGModuleCat R) (ModuleCat R)).map f))
    intro r hr n
    obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective f.hom).mp inferInstance n
    rw [← f.hom.hom.map_smul, hM r hr m, map_zero]

end Quillen.FiniteModuleLocalization.IdealClosedSupport

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion

/-- Scheme isomorphisms give actual coherent restriction equivalences. -/
def coherentIsoEquivalence {Z X : Scheme.{u}} (e : Z ≅ X) :
    FiniteTypeSheaves Z ≌ FiniteTypeSheaves X :=
  CategoryTheory.Equivalence.mk (finiteTypeSheavesRestriction e.inv) (finiteTypeSheavesRestriction
    e.hom)
    (Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules Z)
      (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z)
        (Scheme.Modules.restrictFunctorId.symm ≪≫
          Scheme.Modules.restrictFunctorCongr e.hom_inv_id.symm ≪≫
          Scheme.Modules.restrictFunctorComp e.hom e.inv)))
    (Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
      (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X)
        ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
          Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
          Scheme.Modules.restrictFunctorId)))

variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]
  (R : CommRingCat.{u}) [IsNoetherianRing R]
  (i : Z ⟶ Spec R) [IsClosedImmersion i]

/-- Actual closed pushforward with affine target is full. -/
instance coherentPushforward_affine_full : (coherentPushforward i).Full := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  have : (finiteTypeSheavesRestriction e.inv).IsEquivalence := (coherentIsoEquivalence
    e).isEquivalence_functor
  exact Functor.Full.of_iso (affinePresentationComparison R i I e hi).symm

omit [IsLocallyNoetherian Z] [IsNoetherianRing R] in
/-- The actual essential image is exactly annihilation by the ideal in an
actual quotient presentation of the closed immersion. -/
theorem coherentPushforward_essImage_iff (I : Ideal R)
    (e : Z ≅ Spec (Pushforward.ClosedImmersion.Ideal.closedRing R I)) (hi : i = e.hom ≫
      Pushforward.ClosedImmersion.Ideal.closedMap R I)
    (M : FiniteTypeSheaves (Spec R)) :
    (finiteTypePushforward i).essImage M ↔ Ideal.finiteTypeSheavesKilledBy R I M := by
  let ER := finiteTypeSheavesSpecModuleEquivalence R
  let ES := finiteTypeSheavesSpecModuleEquivalence (Pushforward.ClosedImmersion.Ideal.closedRing
    R I)
  let F := coherentIsoEquivalence e
  let q : R ⟶ Pushforward.ClosedImmersion.Ideal.closedRing R I := CommRingCat.ofHom
    (Ideal.Quotient.mk I)
  have hq : q.hom.Finite := by
    apply (AlgebraicGeometry.IsFinite.SpecMap_iff q).mp
    change AlgebraicGeometry.IsFinite (Pushforward.ClosedImmersion.Ideal.closedMap R I)
    infer_instance
  let c : finiteTypePushforward i ≅
      F.functor ⋙ finiteTypePushforward (Pushforward.ClosedImmersion.Ideal.closedMap R I) :=
    finiteTypePushforwardAffinePresentationComparison R
      (Pushforward.ClosedImmersion.Ideal.closedRing R I) i q hq e hi
  let sq : finiteTypePushforward (Pushforward.ClosedImmersion.Ideal.closedMap R I) ⋙ ER.functor ≅
      ES.functor ⋙ closedRestriction I :=
    finiteTypePushforwardSpecSquare q hq
  change (finiteTypePushforward i).essImage M ↔ killedBy I (ER.functor.obj M)
  constructor
  · rintro ⟨N, ⟨f⟩⟩
    exact (killedBy I).prop_of_iso
      ((sq.app (F.functor.obj N)).symm ≪≫
        ER.functor.mapIso ((c.app N).symm ≪≫ f))
      (closedRestriction_killed I _)
  · intro hM
    let Q : (killedBy I).FullSubcategory := ⟨ER.functor.obj M, hM⟩
    let P := (closedEquivalence I).inverse.obj Q
    let L := ES.inverse.obj P
    refine ⟨F.inverse.obj L, ⟨?_⟩⟩
    exact c.app (F.inverse.obj L) ≪≫
      (finiteTypePushforward (Pushforward.ClosedImmersion.Ideal.closedMap R I)).mapIso
        (F.counitIso.app L) ≪≫
      ER.fullyFaithfulFunctor.preimageIso
        (sq.app L ≪≫
          (closedRestriction I).mapIso (ES.counitIso.app P) ≪≫
          (killedBy I).ι.mapIso ((closedEquivalence I).counitIso.app Q))

/-- The actual affine closed essential image is closed under quotients. -/
instance coherentPushforward_affine_essImage_quotients :
    (coherentPushforward i).essImage.IsClosedUnderQuotients where
  prop_of_epi {M N} f hf hM := by
    obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
    have : (Ideal.finiteTypeSheavesKilledBy R I).IsClosedUnderQuotients := by
      dsimp [Ideal.finiteTypeSheavesKilledBy]
      infer_instance
    exact (coherentPushforward_essImage_iff R i I e hi N).mpr
      ((Ideal.finiteTypeSheavesKilledBy R I).prop_of_epi f
        ((coherentPushforward_essImage_iff R i I e hi M).mp hM))

/-- The actual affine closed pullback unit is epic, because its genuine
right adjoint has quotient-closed essential image. -/
instance coherentAdjunction_affine_unit_epi (M : FiniteTypeSheaves (Spec R)) :
    Epi ((coherentAdjunction i).unit.app M) :=
  ReflectorDevissage.unit_epi_of_essImage_quotient_closed (coherentAdjunction i) M

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
