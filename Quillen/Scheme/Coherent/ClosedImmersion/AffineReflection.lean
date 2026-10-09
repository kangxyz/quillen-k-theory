import Quillen.Scheme.Coherent.ClosedImmersion.GeneralPullback
import Quillen.Devissage.ReflectorFiltration
import Quillen.Scheme.Coherent.ClosedImmersion.IdealPowerFiltration

/-!
# The actual closed reflector on an affine ambient scheme

The quotient presentation identifies the essential image of genuine closed
pushforward with ideal-annihilated coherent sheaves. This concerns the
annihilated objects, rather than all sheaves with the same closed support.
-/
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

namespace Quillen.CoherentScheme.ClosedImmersion.General

/-- Scheme isomorphisms give actual coherent restriction equivalences. -/
def coherentIsoEquivalence {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    [IsLocallyNoetherian X] (e : Z ≅ X) : Coherent Z ≌ Coherent X :=
  CategoryTheory.Equivalence.mk (coherentRestriction e.inv) (coherentRestriction e.hom)
    (Functor.fullyFaithfulCancelRight (coherentToSheaves Z)
      (Functor.isoWhiskerLeft (coherentToSheaves Z)
        (Scheme.Modules.restrictFunctorId.symm ≪≫
          Scheme.Modules.restrictFunctorCongr e.hom_inv_id.symm ≪≫
          Scheme.Modules.restrictFunctorComp e.hom e.inv)))
    (Functor.fullyFaithfulCancelRight (coherentToSheaves X)
      (Functor.isoWhiskerLeft (coherentToSheaves X)
        ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
          Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
          Scheme.Modules.restrictFunctorId)))

variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]
  (R : CommRingCat.{u}) [IsNoetherianRing R]
  (i : Z ⟶ Spec R) [IsClosedImmersion i]

/-- Actual closed pushforward with affine target is full. -/
instance coherentPushforward_affine_full : (coherentPushforward i).Full := by
  obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
  have : (coherentRestriction e.inv).IsEquivalence := (coherentIsoEquivalence e).isEquivalence_functor
  exact Functor.Full.of_iso (affinePresentationComparison R i I e hi).symm

/-- The actual essential image is exactly annihilation by the ideal in an
actual quotient presentation of the closed immersion. -/
theorem coherentPushforward_essImage_iff (I : Ideal R)
    (e : Z ≅ Spec (Ideal.closedRing R I)) (hi : i = e.hom ≫ Ideal.closedMap R I)
    (M : Coherent (Spec R)) :
    (coherentPushforward i).essImage M ↔ Ideal.coherentKilledBy R I M := by
  constructor
  · rintro ⟨N, ⟨f⟩⟩
    exact (Ideal.coherentKilledBy R I).prop_of_iso
      (((affinePresentationComparison R i I e hi).app N).symm ≪≫ f)
        (Ideal.coherentPushforward_killed R I _)
  · intro hM
    let Q : (Ideal.coherentKilledBy R I).FullSubcategory := ⟨M, hM⟩
    let N := (Ideal.coherentClosedEquivalence R I).inverse.obj Q
    let F := coherentIsoEquivalence e
    refine ⟨F.inverse.obj N, ⟨?_⟩⟩
    exact (affinePresentationComparison R i I e hi).app (F.inverse.obj N) ≪≫
      (Ideal.coherentPushforward R I).mapIso (F.counitIso.app N) ≪≫
      (Ideal.coherentKilledBy R I).ι.mapIso
        ((Ideal.coherentClosedEquivalence R I).counitIso.app Q)

/-- The actual affine closed essential image is closed under quotients. -/
instance coherentPushforward_affine_essImage_quotients :
    (coherentPushforward i).essImage.IsClosedUnderQuotients where
  prop_of_epi {M N} f hf hM := by
    obtain ⟨I, e, hi⟩ := (IsClosedImmersion.Spec_iff (f := i)).mp inferInstance
    have : (Ideal.coherentKilledBy R I).IsClosedUnderQuotients := by
      dsimp [Ideal.coherentKilledBy]
      infer_instance
    exact (coherentPushforward_essImage_iff R i I e hi N).mpr
      ((Ideal.coherentKilledBy R I).prop_of_epi f
        ((coherentPushforward_essImage_iff R i I e hi M).mp hM))

/-- The actual affine closed pullback unit is epic, because its genuine
right adjoint has quotient-closed essential image. -/
instance coherentAdjunction_affine_unit_epi (M : Coherent (Spec R)) :
    Epi ((coherentAdjunction i).unit.app M) :=
  ReflectorDevissage.unit_epi_of_essImage_quotient_closed (coherentAdjunction i) M

end Quillen.CoherentScheme.ClosedImmersion.General
