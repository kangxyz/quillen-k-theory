/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.GTheory.FiniteModules.LocalizationNaturality
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.PrincipalBoundaryComparison
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.RingIsoNaturality
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Original principal boundaries under a base-ring isomorphism

A given isomorphism of noetherian commutative rings and an equality carrying
the specified element to the specified target element induce the actual Away
and principal-quotient ring isomorphisms. The scalar/localization square is
proved from tensor extension, scalar restriction and the original ring-map
triangle. Its closed-support comparison is lifted through the fully faithful
category inclusion of the actual torsion kernel.

The resulting statements retain the original native `closedConnectingHom`
and the original public `Scheme.PrincipalClosed.boundaryG` in every degree.
Only the genuine support and affine G-equivalences are cancelled; no ambient
K-group inclusion or assumed boundary square enters the argument.

The current consumer is the actual affine stalk isomorphism, with the original
stalk uniformizer transported to the corresponding localization ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace Quillen.FiniteModuleLocalization.PrincipalRingIso
attribute [local instance] Abelian.hasFiniteBiproducts

private def restrictionExtensionIso {A B : Type u} [CommRing A] [CommRing B] (j : A ≃+* B) :
    ModuleCat.restrictScalars j.symm.toRingHom ≅ ModuleCat.extendScalars j.toRingHom :=
  Adjunction.leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv j.symm).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj j.toRingHom)

variable {R S : CommRingCat.{u}}
  (e : R ≅ S) (r : R) (s : S) (h : e.hom.hom r = s)

/-- The canonical localization isomorphism induced by the given base isomorphism. -/
def awayRingEquiv : Localization.Away r ≃+* Localization.Away s :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers r) (T := Submonoid.powers s)
    (Localization.Away r) (Localization.Away s)
    e.commRingCatIsoToRingEquiv (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers
        ((DFunLike.congr_fun (Iso.commRingCatIsoToRingEquiv_toRingHom e) r).trans h))

/-- The induced Away isomorphism retains the literal base-ring map. -/
theorem awayRingEquiv_algebraMap (a : R) :
    awayRingEquiv e r s h (algebraMap R (Localization.Away r) a) =
      algebraMap S (Localization.Away s) (e.hom.hom a) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ a

/-- The original localization ring-map square commutes. -/
theorem awayRingEquiv_comp_algebraMap :
    (awayRingEquiv e r s h).toRingHom.comp (algebraMap R (Localization.Away r)) =
      (algebraMap S (Localization.Away s)).comp e.hom.hom := by
  ext a
  exact awayRingEquiv_algebraMap e r s h a

/-- The canonical principal-quotient isomorphism induced by the given base isomorphism. -/
def closedRingEquiv : ClosedRing r ≃+* ClosedRing s :=
  Ideal.quotientEquiv (Ideal.span {r}) (Ideal.span {s}) e.commRingCatIsoToRingEquiv (by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun t : S => Ideal.span {t})
      ((DFunLike.congr_fun (Iso.commRingCatIsoToRingEquiv_toRingHom e) r).trans h).symm)

/-- Its inverse carries the original quotient generator to the inverse base-ring image. -/
theorem closedRingEquiv_symm_mk (b : S) :
    (closedRingEquiv e r s h).symm (Ideal.Quotient.mk (Ideal.span {s}) b) =
      Ideal.Quotient.mk (Ideal.span {r}) (e.inv.hom b) := rfl

/-- Actual finite-module scalar restriction along the inverse of the specified ring isomorphism. -/
def transportExact {A B : CommRingCat.{u}} [IsNoetherianRing A] [IsNoetherianRing B]
    (j : A ≅ B) : ExactFunctor (finiteModuleExactStructure.{u,u} A)
      (finiteModuleExactStructure.{u,u} B) :=
  ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact j.inv
    (RingHom.Finite.of_surjective _ j.commRingCatIsoToRingEquiv.symm.surjective)

variable [IsNoetherianRing R] [IsNoetherianRing S]

private def openModuleIso :
    ModuleCat.localizedModuleFunctor (Submonoid.powers r) ⋙
        ModuleCat.restrictScalars (awayRingEquiv e r s h).symm.toRingHom ≅
    ModuleCat.restrictScalars e.inv.hom ⋙
      ModuleCat.localizedModuleFunctor (Submonoid.powers s) :=
  Functor.isoWhiskerRight (ModuleCat.extendScalarsLocalizationIso (Submonoid.powers r)).symm
      (ModuleCat.restrictScalars (awayRingEquiv e r s h).symm.toRingHom) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars (algebraMap R (Localization.Away r)))
      (restrictionExtensionIso (awayRingEquiv e r s h)) ≪≫
    (ModuleCat.extendScalarsComp (algebraMap R (Localization.Away r))
      (awayRingEquiv e r s h).toRingHom).symm ≪≫
    eqToIso (congrArg (fun f : R →+* Localization.Away s => ModuleCat.extendScalars.{u} f)
      (awayRingEquiv_comp_algebraMap e r s h)) ≪≫
    ModuleCat.extendScalarsComp e.hom.hom (algebraMap S (Localization.Away s)) ≪≫
    Functor.isoWhiskerRight (restrictionExtensionIso e.commRingCatIsoToRingEquiv).symm
      (ModuleCat.extendScalars (algebraMap S (Localization.Away s))) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars e.inv.hom)
      (ModuleCat.extendScalarsLocalizationIso (Submonoid.powers s))

private def openOrdinaryIso :
    ((exactFunctor (Submonoid.powers r)).comp
      (transportExact (awayRingEquiv e r s h).toCommRingCatIso)).toFunctor ≅
    ((transportExact e).comp (exactFunctor (Submonoid.powers s))).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ((openModuleIso e r s h).app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact (openModuleIso e r s h).hom.naturality f.hom)

private def supportTransportExact := inducedSupportedExactFunctorOfSquare
  (Submonoid.powers r) (Submonoid.powers s) (transportExact e)
  (transportExact (awayRingEquiv e r s h).toCommRingCatIso) (openOrdinaryIso e r s h)

private def closedModuleIso :
    ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})) ⋙
      ModuleCat.restrictScalars e.inv.hom ≅
    ModuleCat.restrictScalars (closedRingEquiv e r s h).symm.toRingHom ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {s})) :=
  (ModuleCat.restrictScalarsComp e.inv.hom (Ideal.Quotient.mk (Ideal.span {r}))).symm ≪≫
    ModuleCat.restrictScalarsComp' (Ideal.Quotient.mk (Ideal.span {s}))
      (closedRingEquiv e r s h).symm.toRingHom
      ((Ideal.Quotient.mk (Ideal.span {r})).comp e.inv.hom) (by
        ext b
        exact (closedRingEquiv_symm_mk e r s h b).symm)

private def closedOrdinaryIso :
    ((closedRestrictionExact r).comp (transportExact e)).toFunctor ≅
    ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).comp
      (closedRestrictionExact s)).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ((closedModuleIso e r s h).app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact (closedModuleIso e r s h).hom.naturality f.hom)

private def supportClosedIso :
    ((smallClosedToSupportExact r).comp (supportTransportExact e r s h)).toFunctor ≅
    ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallModel.comp
      (smallClosedToSupportExact s)).toFunctor := by
  apply Functor.fullyFaithfulCancelRight (smallTorsion (Submonoid.powers s)).ι
  change (closedRestrictionExact r).smallModel.toFunctor ⋙
    (transportExact e).smallModel.toFunctor ≅ _
  exact (ExactFunctor.smallModelCompIso (closedRestrictionExact r) (transportExact e)).symm ≪≫
    ExactFunctor.smallModelNatIso (closedOrdinaryIso e r s h) ≪≫
    ExactFunctor.smallModelCompIso (transportExact (closedRingEquiv e r s h).toCommRingCatIso)
      (closedRestrictionExact s)

private theorem supportClosedKMap (n : ℕ) :
    ((supportTransportExact e r s h).KMap n).comp (closedSupportGEquiv r n).toMonoidHom =
      (closedSupportGEquiv s n).toMonoidHom.comp
        ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallKMap n) := by
  have hk := ExactFunctor.KMap_eq_of_natIso (supportClosedIso e r s h) n
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_comp] at hk
  apply MonoidHom.ext
  intro a
  have hr := DFunLike.congr_fun (closedSupportGEquiv_coe r n) a
  have hs := DFunLike.congr_fun (closedSupportGEquiv_coe s n)
    ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallKMap n a)
  change closedSupportGEquiv r n a = (smallClosedToSupportExact r).KMap n a at hr
  change closedSupportGEquiv s n
      ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallKMap n a) =
    (smallClosedToSupportExact s).KMap n
      ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallKMap n a) at hs
  exact (congrArg ((supportTransportExact e r s h).KMap n) hr).trans
    ((DFunLike.congr_fun hk a).trans hs.symm)

/-- The original native principal-closed boundaries commute with the prescribed scalar
restrictions in every degree. -/
theorem closedConnectingHom_naturality (n : ℕ) :
    ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallKMap n).comp
      (closedConnectingHom r n) =
    (closedConnectingHom s n).comp
      ((transportExact (awayRingEquiv e r s h).toCommRingCatIso).smallKMap (n + 1)) := by
  apply MonoidHom.ext
  intro a
  apply (closedSupportGEquiv s n).injective
  have hs := DFunLike.congr_fun (supportClosedKMap e r s h n) (closedConnectingHom r n a)
  have hr : closedSupportGEquiv r n (closedConnectingHom r n a) =
      connectingHom (Submonoid.powers r) n a := (closedSupportGEquiv r n).apply_symm_apply _
  have ht : closedSupportGEquiv s n (closedConnectingHom s n
      ((transportExact (awayRingEquiv e r s h).toCommRingCatIso).smallKMap (n + 1) a)) =
    connectingHom (Submonoid.powers s) n
      ((transportExact (awayRingEquiv e r s h).toCommRingCatIso).smallKMap (n + 1) a) :=
    (closedSupportGEquiv s n).apply_symm_apply _
  have hn := DFunLike.congr_fun (connectingHom_naturality (Submonoid.powers r)
    (Submonoid.powers s) (transportExact e)
    (transportExact (awayRingEquiv e r s h).toCommRingCatIso) (openOrdinaryIso e r s h) n) a
  exact hs.symm.trans ((congrArg ((supportTransportExact e r s h).KMap n) hr).trans
    (hn.trans ht.symm))

/-- The original public principal-closed scheme boundaries commute with the actual
induced open and closed isomorphism pullbacks, in every degree. -/
theorem principalBoundaryG_naturality (n : ℕ) :
    (Scheme.pullbackG (Spec.map (closedRingEquiv e r s h).toCommRingCatIso.hom) n).comp
      (Scheme.PrincipalClosed.boundaryG R r n) =
    (Scheme.PrincipalClosed.boundaryG S s n).comp
      (Scheme.pullbackG (Spec.map (awayRingEquiv e r s h).toCommRingCatIso.hom) (n + 1)) := by
  apply MonoidHom.ext
  intro a
  apply (publicSpecGRingEquiv (CommRingCat.of (ClosedRing s)) n).injective
  have hc := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback (closedRingEquiv e r s h) n)
      (Scheme.PrincipalClosed.boundaryG R r n a)
  have hr := DFunLike.congr_fun (publicSpecGRingEquiv_principalClosed_boundaryG R r n) a
  have hn := DFunLike.congr_fun (closedConnectingHom_naturality e r s h n)
    (publicSpecGRingEquiv (CommRingCat.of (Localization.Away r)) (n + 1) a)
  have ho := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback (awayRingEquiv e r s h) (n + 1)) a
  have ht := DFunLike.congr_fun (publicSpecGRingEquiv_principalClosed_boundaryG S s n)
    (Scheme.pullbackG (Spec.map (awayRingEquiv e r s h).toCommRingCatIso.hom) (n + 1) a)
  exact hc.trans ((congrArg
    ((transportExact (closedRingEquiv e r s h).toCommRingCatIso).smallKMap n) hr).trans
    (hn.trans ((congrArg (closedConnectingHom s n) ho.symm).trans ht.symm)))

end Quillen.FiniteModuleLocalization.PrincipalRingIso
