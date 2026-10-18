/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.GTheory.Dedekind.LocalDvrBoundaryNaturality
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.PrincipalBoundaryComparison
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.RingIsoNaturality
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Literal principal-open boundaries and the original native local-DVR boundary

At a nonzero prime of a Dedekind domain, an irreducible element of the actual
local ring gives the original principal-closed scheme boundary. Its canonical
fraction-field and quotient-residue ring isomorphisms retain the original
geometric pullbacks. Under canonical affine G-comparison, this composite is
the original `localDvrBoundary` in every degree.

The supported comparison uses the actual quotient ideal equality, the original
quotient-residue inclusion isomorphism and a lift through the fully faithful
torsion-category inclusion. The native support equivalence is used only with
its proved original forward map. The generic localization-isomorphism helper
retains ordinary tensor comparisons and original boundary naturality.

The arbitrary-field theorem keeps the supplied fraction field and algebra
structure. Its native generic map is actual scalar restriction along the
canonical fraction-field equivalence. No replacement boundary, arbitrary
group isomorphism or choice of sign is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped nonZeroDivisors

namespace Quillen.DedekindLocalDvr.PrincipalComparison
attribute [local instance] Abelian.hasFiniteBiproducts
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (S T : Submonoid R) (e : Localization S ≃ₐ[R] Localization T)

private def targetExact := ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
  (CommRingCat.ofHom e.symm.toRingHom) (RingHom.Finite.of_surjective _ e.symm.surjective)

private def restrictionExtensionIso :
    ModuleCat.restrictScalars e.symm.toRingHom ≅ ModuleCat.extendScalars e.toRingHom :=
  Adjunction.leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm.toRingEquiv).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom)

private def moduleIso :
    ModuleCat.localizedModuleFunctor S ⋙ ModuleCat.restrictScalars e.symm.toRingHom ≅
      ModuleCat.localizedModuleFunctor T :=
  Functor.isoWhiskerRight (localizationTensorIso S).symm
      (ModuleCat.restrictScalars e.symm.toRingHom) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars (algebraMap R (Localization S)))
      (restrictionExtensionIso S T e) ≪≫
    (ModuleCat.extendScalarsComp (algebraMap R (Localization S)) e.toRingHom).symm ≪≫
    eqToIso (congrArg (fun f : R →+* Localization T => ModuleCat.extendScalars.{u} f)
      (by ext r; exact e.commutes r)) ≪≫
    localizationTensorIso T

private def ordinarySquare :
    ((FiniteModuleLocalization.exactFunctor S).comp (targetExact S T e)).toFunctor ≅
    ((ExactFunctor.id (ModuleCat.finiteModuleExactStructure.{u,u} R)).comp
      (FiniteModuleLocalization.exactFunctor T)).toFunctor :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ((moduleIso S T e).app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact (moduleIso S T e).hom.naturality f.hom)

private def supportExact := FiniteModuleLocalization.inducedSupportedExactFunctorOfSquare S T
  (ExactFunctor.id (ModuleCat.finiteModuleExactStructure.{u,u} R))
  (targetExact S T e) (ordinarySquare S T e)

private theorem connectingHom_square (n : ℕ) :
    ((supportExact S T e).KMap n).comp (FiniteModuleLocalization.connectingHom S n) =
      (FiniteModuleLocalization.connectingHom T n).comp ((targetExact S T e).smallKMap (n + 1)) :=
  FiniteModuleLocalization.connectingHom_naturality S T
    (ExactFunctor.id (ModuleCat.finiteModuleExactStructure.{u,u} R))
    (targetExact S T e) (ordinarySquare S T e) n
end Quillen.DedekindLocalDvr.PrincipalComparison


namespace Quillen.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local instance : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _
variable {π : (Localization.AtPrime p.asIdeal)} (hπ : Irreducible π)
include hπ

/-- The native fraction ring is the actual localization away from the chosen irreducible. -/
theorem principalFraction_isLocalizationAway :
    IsLocalization.Away π (FractionRing (Localization.AtPrime p.asIdeal)) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := FractionRing (Localization.AtPrime p.asIdeal))
    (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
  · infer_instance
  · intro a ha
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp ha) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

/-- The canonical algebra equivalence from the actual principal open to the native fraction ring. -/
def principalAwayFractionEquiv :
    Localization.Away π ≃ₐ[Localization.AtPrime p.asIdeal]
      FractionRing (Localization.AtPrime p.asIdeal) :=
  letI := principalFraction_isLocalizationAway R p hπ
  IsLocalization.algEquiv (Submonoid.powers π) _ _

/-- The actual principal quotient identifies with the prescribed local residue field. -/
def principalClosedResidueEquiv :
    FiniteModuleLocalization.ClosedRing π ≃+* p.asIdeal.ResidueField :=
  Ideal.quotEquivOfEq hπ.maximalIdeal_eq.symm

/-- Actual scalar restriction along the inverse of the prescribed quotient-residue equivalence. -/
def principalResidueRestrictionExact := ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
  (CommRingCat.ofHom (principalClosedResidueEquiv R p hπ).symm.toRingHom)
  (RingHom.Finite.of_surjective _ (principalClosedResidueEquiv R p hπ).symm.surjective)

/-- Actual scalar restriction along the inverse canonical principal-open fraction equivalence. -/
def principalFractionRestrictionExact := ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
  (CommRingCat.ofHom (principalAwayFractionEquiv R p hπ).symm.toRingHom)
  (RingHom.Finite.of_surjective _ (principalAwayFractionEquiv R p hπ).symm.surjective)

private def principalSupportExact := PrincipalComparison.supportExact
  (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (principalAwayFractionEquiv R p hπ)

private def closedOrdinaryIso :
    (FiniteModuleLocalization.closedRestrictionExact π).toFunctor ≅
    ((principalResidueRestrictionExact R p hπ).comp
      (ModuleCat.FiniteLocalization.IdealClosedSupport.closedRestrictionExact
        (localPoint R p).asIdeal)).toFunctor := by
  let e := principalClosedResidueEquiv R p hπ
  have he : Ideal.Quotient.mk (Ideal.span {π}) =
      e.symm.toRingHom.comp (Ideal.Quotient.mk (localPoint R p).asIdeal) := by
    ext r
    apply e.injective
    change e (Ideal.Quotient.mk (Ideal.span {π}) r) =
      e (e.symm (Ideal.Quotient.mk (localPoint R p).asIdeal r))
    rw [e.apply_symm_apply]
    exact Ideal.quotEquivOfEq_mk hπ.maximalIdeal_eq.symm r
  let η := ModuleCat.restrictScalarsComp'.{u}
    (Ideal.Quotient.mk (localPoint R p).asIdeal) e.symm.toRingHom
    (Ideal.Quotient.mk (Ideal.span {π})) he
  exact NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (η.app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact η.hom.naturality f.hom)

private def supportClosedIso :
    ((FiniteModuleLocalization.smallClosedToSupportExact π).comp
      (principalSupportExact R p hπ)).toFunctor ≅
    ((principalResidueRestrictionExact R p hπ).smallModel.comp
      (DedekindResidue.quotientResidueSupportExactFunctor (Localization.AtPrime p.asIdeal)
        (localPoint R p))).toFunctor := by
  apply Functor.fullyFaithfulCancelRight
    (FiniteModuleLocalization.smallTorsion (nonZeroDivisors (Localization.AtPrime p.asIdeal))).ι
  change (FiniteModuleLocalization.closedRestrictionExact π).smallModel.toFunctor ⋙
      (ExactFunctor.id (ModuleCat.finiteModuleExactStructure.{u,u}
        (Localization.AtPrime p.asIdeal))).smallModel.toFunctor ≅ _
  exact Functor.isoWhiskerLeft
      (FiniteModuleLocalization.closedRestrictionExact π).smallModel.toFunctor
      (ExactFunctor.smallModelIdIso
        (ModuleCat.finiteModuleExactStructure.{u,u} (Localization.AtPrime p.asIdeal))) ≪≫
    Functor.rightUnitor (FiniteModuleLocalization.closedRestrictionExact π).smallModel.toFunctor ≪≫
    ExactFunctor.smallModelNatIso (closedOrdinaryIso R p hπ) ≪≫
    ExactFunctor.smallModelCompIso (principalResidueRestrictionExact R p hπ)
      (ModuleCat.FiniteLocalization.IdealClosedSupport.closedRestrictionExact
        (localPoint R p).asIdeal) ≪≫
    Functor.isoWhiskerLeft (principalResidueRestrictionExact R p hπ).smallModel.toFunctor
      (quotientResidueSupportInclusionIso (Localization.AtPrime p.asIdeal)
        (localPoint R p)).symm


private theorem supportClosedKMap (n : ℕ) :
    ((principalSupportExact R p hπ).KMap n).comp
      (FiniteModuleLocalization.closedSupportGEquiv π n).toMonoidHom =
    (localResidueSupportKEquiv R p n).toMonoidHom.comp
      ((principalResidueRestrictionExact R p hπ).smallKMap n) := by
  have h := ExactFunctor.KMap_eq_of_natIso (supportClosedIso R p hπ) n
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_comp] at h
  apply MonoidHom.ext
  intro a
  have hl := DFunLike.congr_fun (FiniteModuleLocalization.closedSupportGEquiv_coe π n) a
  change FiniteModuleLocalization.closedSupportGEquiv π n a =
    (FiniteModuleLocalization.smallClosedToSupportExact π).KMap n a at hl
  change (principalSupportExact R p hπ).KMap n
      (FiniteModuleLocalization.closedSupportGEquiv π n a) =
    localResidueSupportKEquiv R p n ((principalResidueRestrictionExact R p hπ).smallKMap n a)
  exact (congrArg ((principalSupportExact R p hπ).KMap n) hl).trans
    ((DFunLike.congr_fun h a).trans
      (localResidueSupportKEquiv_apply R p n
        ((principalResidueRestrictionExact R p hπ).smallKMap n a)).symm)

/-- The original native principal-closed boundary agrees with the original local-DVR boundary
after the prescribed scalar restrictions, in every degree. -/
theorem principalBoundary_nativeBoundary (n : ℕ) :
    ((principalResidueRestrictionExact R p hπ).smallKMap n).comp
      (FiniteModuleLocalization.closedConnectingHom π n) =
    (localDvrBoundary R p n).comp
      ((principalFractionRestrictionExact R p hπ).smallKMap (n + 1)) := by
  apply MonoidHom.ext
  intro a
  apply (localResidueSupportKEquiv R p n).injective
  have hs := DFunLike.congr_fun (supportClosedKMap R p hπ n)
    (FiniteModuleLocalization.closedConnectingHom π n a)
  have hclosed : FiniteModuleLocalization.closedSupportGEquiv π n
      (FiniteModuleLocalization.closedConnectingHom π n a) =
    FiniteModuleLocalization.connectingHom (Submonoid.powers π) n a :=
    (FiniteModuleLocalization.closedSupportGEquiv π n).apply_symm_apply _
  have hn := DFunLike.congr_fun
    (PrincipalComparison.connectingHom_square
      (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
      (principalAwayFractionEquiv R p hπ) n) a
  have hlocal : localResidueSupportKEquiv R p n
      (localDvrBoundary R p n ((principalFractionRestrictionExact R p hπ).smallKMap (n + 1) a)) =
    FiniteModuleLocalization.connectingHom (nonZeroDivisors (Localization.AtPrime p.asIdeal)) n
      ((principalFractionRestrictionExact R p hπ).smallKMap (n + 1) a) :=
    (localResidueSupportKEquiv R p n).apply_symm_apply _
  exact hs.symm.trans
    ((congrArg ((principalSupportExact R p hπ).KMap n) hclosed).trans (hn.trans hlocal.symm))

end Quillen.DedekindLocalDvr


namespace Quillen.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
variable {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)

private def principalFractionReverseExact :=
  ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
  (CommRingCat.ofHom (principalAwayFractionEquiv R p hπ).toRingHom)
  (RingHom.Finite.of_surjective _ (principalAwayFractionEquiv R p hπ).surjective)

private def openRoundTripIso :
    ((principalFractionReverseExact R p hπ).comp
      (principalFractionRestrictionExact R p hπ)).toFunctor ≅
    (ExactFunctor.id (ModuleCat.finiteModuleExactStructure.{u,u}
      (FractionRing (Localization.AtPrime p.asIdeal)))).toFunctor := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (principalAwayFractionEquiv R p hπ).toRingEquiv
  exact NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (E.unitIso.symm.app M.obj)) (by
    intro M N f
    apply ObjectProperty.hom_ext
    exact E.unitIso.inv.naturality f.hom)

private theorem openRoundTripKMap (n : ℕ) :
    ((principalFractionRestrictionExact R p hπ).smallKMap n).comp
      ((principalFractionReverseExact R p hπ).smallKMap n) =
      MonoidHom.id _ := by
  have h := ExactFunctor.smallKMap_eq_of_natIso (openRoundTripIso R p hπ) n
  simpa only [ExactFunctor.smallKMap_comp, ExactFunctor.smallKMap_id] using h

/-- The literal principal-closed scheme boundary, with its original generic and closed
isomorphism pullbacks, agrees with the native local-DVR boundary in every degree. -/
theorem principalSchemeBoundary_nativeBoundary (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of (FractionRing (Localization.AtPrime p.asIdeal)))) (n + 1)) :
    publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n
          (Scheme.pullbackG
            (Spec.map (principalAwayFractionEquiv R p hπ).toRingEquiv.symm.toCommRingCatIso.hom)
            (n + 1) a))) =
    localDvrBoundary R p n
      (publicSpecGRingEquiv (CommRingCat.of (FractionRing (Localization.AtPrime p.asIdeal)))
        (n + 1) a) := by
  let z := Scheme.pullbackG
    (Spec.map (principalAwayFractionEquiv R p hπ).toRingEquiv.symm.toCommRingCatIso.hom) (n + 1) a
  have hc := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback (principalClosedResidueEquiv R p hπ) n)
      (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n z)
  have hp := DFunLike.congr_fun
    (publicSpecGRingEquiv_principalClosed_boundaryG
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n) z
  have hn := DFunLike.congr_fun (principalBoundary_nativeBoundary R p hπ n)
    (publicSpecGRingEquiv (CommRingCat.of (Localization.Away π)) (n + 1) z)
  have ho := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback
      (principalAwayFractionEquiv R p hπ).toRingEquiv.symm (n + 1)) a
  have hr := DFunLike.congr_fun (openRoundTripKMap R p hπ (n + 1))
    (publicSpecGRingEquiv
      (CommRingCat.of (FractionRing (Localization.AtPrime p.asIdeal))) (n + 1) a)
  exact hc.trans ((congrArg ((principalResidueRestrictionExact R p hπ).smallKMap n) hp).trans
    (hn.trans (congrArg (localDvrBoundary R p n)
      ((congrArg ((principalFractionRestrictionExact R p hπ).smallKMap (n + 1)) ho).trans hr))))
end Quillen.DedekindLocalDvr


namespace Quillen.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local instance : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _
variable (K : Type u) [Field K] [Algebra (Localization.AtPrime p.asIdeal) K]
  [IsFractionRing (Localization.AtPrime p.asIdeal) K]
variable {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)
include hπ

/-- The supplied fraction field is the actual localization away from the chosen irreducible. -/
theorem principalField_isLocalizationAway : IsLocalization.Away π K := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := K)
    (Submonoid.powers π) (nonZeroDivisors (Localization.AtPrime p.asIdeal))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
  · infer_instance
  · intro a ha
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp ha) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

/-- The canonical principal-open equivalence to the supplied actual fraction field. -/
def principalAwayFieldEquiv : Localization.Away π ≃ₐ[Localization.AtPrime p.asIdeal] K :=
  letI := principalField_isLocalizationAway R p K hπ
  IsLocalization.algEquiv (Submonoid.powers π) _ _

omit hπ in
/-- The canonical algebra equivalence from the native fraction ring to the supplied field. -/
def localFractionFieldEquiv :
    FractionRing (Localization.AtPrime p.asIdeal) ≃ₐ[Localization.AtPrime p.asIdeal] K :=
  IsLocalization.algEquiv (nonZeroDivisors (Localization.AtPrime p.asIdeal)) _ _

private theorem inverseAlgEquiv :
    (principalAwayFieldEquiv R p K hπ).symm =
      (localFractionFieldEquiv R p K).symm.trans (principalAwayFractionEquiv R p hπ).symm := by
  ext x
  have h : (principalAwayFieldEquiv R p K hπ).symm.toAlgHom =
      ((localFractionFieldEquiv R p K).symm.trans
        (principalAwayFractionEquiv R p hπ).symm).toAlgHom :=
    (IsLocalization.algHom_subsingleton (nonZeroDivisors (Localization.AtPrime p.asIdeal))).elim _ _
  exact DFunLike.congr_fun h x

private theorem inverseSpecTriangle :
    Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom =
      Spec.map (principalAwayFractionEquiv R p hπ).symm.toRingEquiv.toCommRingCatIso.hom ≫
        Spec.map (localFractionFieldEquiv R p K).symm.toRingEquiv.toCommRingCatIso.hom := by
  change Spec.map (CommRingCat.ofHom (principalAwayFieldEquiv R p K hπ).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (principalAwayFractionEquiv R p hπ).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (localFractionFieldEquiv R p K).symm.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : K →+* Localization.Away π => Spec.map (CommRingCat.ofHom f))
    (congrArg (fun e : K ≃ₐ[Localization.AtPrime p.asIdeal] Localization.Away π =>
      e.toRingHom) (inverseAlgEquiv R p K hπ))

omit hπ in
private theorem pullbackG_congr {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] {f g : X ⟶ Y}
    [Flat f] [Flat g] (h : f = g) (n : ℕ) : Scheme.pullbackG f n = Scheme.pullbackG g n := by
  subst g
  rfl

/-- The literal principal boundary with the supplied actual fraction field agrees with
the original native local-DVR boundary after canonical inverse field transport, in every degree. -/
theorem principalSchemeBoundary_nativeBoundary_field (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of K)) (n + 1)) :
    publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n
          (Scheme.pullbackG
            (Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom)
            (n + 1) a))) =
    localDvrBoundary R p n
      ((ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
        (CommRingCat.ofHom (localFractionFieldEquiv R p K).toRingHom)
        (RingHom.Finite.of_surjective _ (localFractionFieldEquiv R p K).surjective)).smallKMap
          (n + 1)
          (publicSpecGRingEquiv (CommRingCat.of K) (n + 1) a)) := by
  have hg : Scheme.pullbackG
      (Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom) (n + 1) =
    (Scheme.pullbackG
      (Spec.map (principalAwayFractionEquiv R p hπ).symm.toRingEquiv.toCommRingCatIso.hom)
      (n + 1)).comp
        (Scheme.pullbackG
          (Spec.map (localFractionFieldEquiv R p K).symm.toRingEquiv.toCommRingCatIso.hom)
          (n + 1)) := by
    exact (pullbackG_congr (inverseSpecTriangle R p K hπ) (n + 1)).trans
      (Scheme.pullbackG_comp _ _ (n + 1))
  have hz := DFunLike.congr_fun hg a
  have hf := DFunLike.congr_fun
    (publicSpecGRingEquiv_ringIso_pullback
      (localFractionFieldEquiv R p K).symm.toRingEquiv (n + 1)) a
  exact (congrArg (fun z => publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n z))) hz).trans
    ((principalSchemeBoundary_nativeBoundary R p hπ n
      (Scheme.pullbackG
        (Spec.map (localFractionFieldEquiv R p K).symm.toRingEquiv.toCommRingCatIso.hom)
        (n + 1) a)).trans (congrArg (localDvrBoundary R p n) hf))
end Quillen.DedekindLocalDvr
