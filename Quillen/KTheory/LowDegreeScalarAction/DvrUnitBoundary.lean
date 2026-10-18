/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.PrincipalUnitBoundary
public import Quillen.GTheory.Dedekind.PrincipalDvrBoundaryComparison

/-!
# Ordered unit and uniformizer values under the original local DVR boundary

Actual restriction along a coefficient-ring isomorphism preserves the original
scalar operations, positive rank-one cubes, and canonically lowered unit products.
The original principal/local-DVR boundary square then transports the ordered
principal formula to the actual canonical fraction field and native residue field.
Only after canonical promotion of the positive residue cube is its original
determinant applied. For a supplied fraction field, the original inverse field
restriction is retained exactly as in the native supplied-field boundary square.

Reverse order, the Steinberg relation for the scalar product, and identification
with Milnor or marked Quillen symbols are separate questions.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u s
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open Quillen.FiniteModuleLocalization
open scoped ZeroObject nonZeroDivisors

namespace Quillen.LowDegreeScalarAction.DvrUnitBoundary

section RingIsomorphism
variable {A B : Type u} [CommRing A] [CommRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B)

/-- The original exact restriction along the inverse coefficient-ring isomorphism. -/
def ringTransportExact : ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} A)
    (ModuleCat.finiteModuleExactStructure.{u, u} B) :=
  ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
    (CommRingCat.ofHom e.symm.toRingHom) (RingHom.Finite.of_surjective _ e.symm.surjective)

private def rankOneTransportIso :
    (ringTransportExact e).toFunctor.obj (FGModuleCat.of A (Fin 1 → A)) ≅
      FGModuleCat.of B (Fin 1 → B) := by
  let M := ((ringTransportExact e).toFunctor.obj (FGModuleCat.of A (Fin 1 → A))).obj
  let l : M ≃ₗ[B] (Fin 1 → B) := {
    toFun := fun x i => e (x i)
    invFun := fun y i => e.symm (y i)
    left_inv := by
      intro x
      change (fun i => e.symm (e (x i))) = x
      funext i
      exact e.symm_apply_apply (x i)
    right_inv := by intro y; ext i; exact e.apply_symm_apply (y i)
    map_add' := by intro x y; ext i; exact map_add e (x i) (y i)
    map_smul' := by
      intro b x
      ext i
      change e (e.symm b * x i) = b * e (x i)
      rw [map_mul, e.apply_symm_apply] }
  exact ObjectProperty.isoMk _ l.toModuleIso

private theorem ordinary_scalar (a : Aˣ) (M : FGModuleCat.{u} A) :
    (ringTransportExact e).toFunctor.map ((scalarNatAut A (FGModuleCat.{u} A) a).hom.app M) =
      (scalarNatAut B (FGModuleCat.{u} B) (Units.map e.toMonoidHom a)).hom.app
        ((ringTransportExact e).toFunctor.obj M) := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (a : A) • (show M from x) = e.symm (e (a : A)) • (show M from x)
  rw [e.symm_apply_apply]

section Models
variable [EssentiallySmall.{s} (FGModuleCat.{u} A)]
  [EssentiallySmall.{s} (FGModuleCat.{u} B)]

private theorem small_scalar (a : Aˣ) (X : SmallModel.{s} (FGModuleCat.{u} A)) :
    (ringTransportExact e).smallModel.{s}.toFunctor.map
        ((smallModelScalarNatAut.{u, u + 1, u, s} A (FGModuleCat.{u} A) a).hom.app X) =
      (smallModelScalarNatAut.{u, u + 1, u, s} B (FGModuleCat.{u} B)
        (Units.map e.toMonoidHom a)).hom.app
          ((ringTransportExact e).smallModel.{s}.toFunctor.obj X) := by
  change (equivSmallModel.{s} (FGModuleCat.{u} B)).functor.map
    ((ringTransportExact e).toFunctor.map
      ((equivSmallModel.{s} (FGModuleCat.{u} A)).inverse.map
        ((smallModelScalarNatAut.{u, u + 1, u, s} A (FGModuleCat.{u} A) a).hom.app X))) = _
  rw [smallModelScalarNatAut_map_hom]
  change (equivSmallModel.{s} (FGModuleCat.{u} B)).functor.map
    ((ringTransportExact e).toFunctor.map
      ((scalarNatAut A (FGModuleCat.{u} A) a).hom.app
        ((equivSmallModel.{s} (FGModuleCat.{u} A)).inverse.obj X))) = _
  rw [ordinary_scalar]
  exact smallModelScalarNatAut_functor_map_hom.{u, u + 1, u, s} B (FGModuleCat.{u} B)
    (Units.map e.toMonoidHom a) _

private theorem rankOneClass_transport :
    (ringTransportExact e).smallKMap.{s} 0
        ((ModuleCat.finiteModuleExactStructure.{u, u} A).smallModel.{s}.kZeroObjectClass
          ((equivSmallModel.{s} (FGModuleCat.{u} A)).functor.obj
            (FGModuleCat.of A (Fin 1 → A)))) =
      (ModuleCat.finiteModuleExactStructure.{u, u} B).smallModel.{s}.kZeroObjectClass
        ((equivSmallModel.{s} (FGModuleCat.{u} B)).functor.obj
          (FGModuleCat.of B (Fin 1 → B))) := by
  change (ringTransportExact e).smallModel.{s}.KMap 0 _ = _
  rw [ExactFunctor.KMap_kZeroObjectClass]
  apply ExactStructure.kZeroObjectClass_iso
  exact (equivSmallModel.{s} (FGModuleCat.{u} B)).functor.mapIso
    (((ringTransportExact e).toFunctor.mapIso
      ((equivSmallModel.{s} (FGModuleCat.{u} A)).unitIso.app
        (FGModuleCat.of A (Fin 1 → A))).symm) ≪≫ rankOneTransportIso e)

private theorem scalarZero_transport (a : Aˣ)
    (z : (ModuleCat.finiteModuleExactStructure.{u, u} A).SmallK.{s} 0) :
    (ringTransportExact e).smallKMap.{s} 1
        (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, s} A
          (ModuleCat.finiteModuleExactStructure.{u, u} A) a z) =
      ScalarUnit.smallModelKZeroAction.{u, u + 1, u, s} B
        (ModuleCat.finiteModuleExactStructure.{u, u} B) (Units.map e.toMonoidHom a)
        ((ringTransportExact e).smallKMap.{s} 0 z) :=
  ExactNaturality.kZeroAction_natural.{s, s} (ringTransportExact e).smallModel.{s}
    (smallModelScalarNatAut.{u, u + 1, u, s} A (FGModuleCat.{u} A) a)
    (smallModelScalarNatAut.{u, u + 1, u, s} B (FGModuleCat.{u} B) (Units.map e.toMonoidHom a))
    (small_scalar e a) z

private theorem scalarOne_transport (a : Aˣ)
    (z : (ModuleCat.finiteModuleExactStructure.{u, u} A).SmallK.{s} 1) :
    (ringTransportExact e).smallKMap.{s} 2
        (ScalarUnit.smallModelKOneAction.{u, u + 1, u, s} A
          (ModuleCat.finiteModuleExactStructure.{u, u} A) a z) =
      ScalarUnit.smallModelKOneAction.{u, u + 1, u, s} B
        (ModuleCat.finiteModuleExactStructure.{u, u} B) (Units.map e.toMonoidHom a)
        ((ringTransportExact e).smallKMap.{s} 1 z) :=
  ExactNaturality.kOneAction_natural.{s, s} (ringTransportExact e).smallModel.{s}
    (smallModelScalarNatAut.{u, u + 1, u, s} A (FGModuleCat.{u} A) a)
    (smallModelScalarNatAut.{u, u + 1, u, s} B (FGModuleCat.{u} B) (Units.map e.toMonoidHom a))
    (small_scalar e a) z

end Models

/-- Actual inverse-isomorphism restriction preserves the literal lower positive
rank-one scalar cube, at the mapped original coefficient. -/
theorem rankOnePositiveCube_ringIso (a : Aˣ) :
    (ringTransportExact e).smallKMap.{u} 1 (PrincipalUnitBoundary.rankOnePositiveCube A a) =
      PrincipalUnitBoundary.rankOnePositiveCube B (Units.map e.toMonoidHom a) := by
  apply inv_injective
  rw [← map_inv, ← PrincipalUnitBoundary.rankOneObjectClass_scalar,
    ← PrincipalUnitBoundary.rankOneObjectClass_scalar, scalarZero_transport]
  rw [show (ringTransportExact e).smallKMap.{u} 0
      (PrincipalUnitBoundary.rankOneObjectClass A) = PrincipalUnitBoundary.rankOneObjectClass B
    from rankOneClass_transport e]

private theorem upperUnitKOne_ringIso (b : Aˣ) :
    (ringTransportExact e).smallKMap.{u + 1} 1 (DvrSymbols.upperUnitKOne A b) =
      DvrSymbols.upperUnitKOne B (Units.map e.toMonoidHom b) := by
  unfold DvrSymbols.upperUnitKOne ScalarUnit.upperFiniteModuleKZeroAction
  rw [map_inv, scalarZero_transport]
  congr 2
  unfold DvrSymbols.upperRankOneClass
  exact rankOneClass_transport.{u, u + 1} e

private theorem upperUnitProduct_ringIso (a b : Aˣ) :
    (ringTransportExact e).smallKMap.{u + 1} 2 (DvrSymbols.upperUnitProduct A a b) =
      DvrSymbols.upperUnitProduct B (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom b) := by
  unfold DvrSymbols.upperUnitProduct ScalarUnit.upperFiniteModuleKOneAction
  rw [scalarOne_transport, upperUnitKOne_ringIso]

/-- Actual restriction along the inverse ring isomorphism preserves the same
canonically lowered original upper unit product. -/
theorem loweredUnitProduct_ringIso (a b : Aˣ) :
    (ringTransportExact e).smallKMap.{u} 2 (DvrSymbols.loweredUnitProduct A a b) =
      DvrSymbols.loweredUnitProduct B (Units.map e.toMonoidHom a) (Units.map e.toMonoidHom b) := by
  apply ((ModuleCat.finiteModuleExactStructure.{u, u}
    B).smallKUniverseEquiv.{u, u + 1} 2).injective
  have h := DFunLike.congr_fun
    (ExactFunctor.smallKUniverseEquiv_naturality.{u, u + 1} (ringTransportExact e) 2)
      (DvrSymbols.loweredUnitProduct A a b)
  change (ringTransportExact e).smallKMap.{u + 1} 2
      (((ModuleCat.finiteModuleExactStructure.{u, u} A).smallKUniverseEquiv.{u, u + 1} 2)
        (DvrSymbols.loweredUnitProduct A a b)) =
    ((ModuleCat.finiteModuleExactStructure.{u, u} B).smallKUniverseEquiv.{u, u + 1} 2)
      ((ringTransportExact e).smallKMap.{u} 2 (DvrSymbols.loweredUnitProduct A a b)) at h
  rw [show ((ModuleCat.finiteModuleExactStructure.{u, u}
      B).smallKUniverseEquiv.{u, u + 1} 2) (DvrSymbols.loweredUnitProduct B _ _) =
        DvrSymbols.upperUnitProduct B _ _ from MulEquiv.apply_symm_apply _ _]
  rw [← h]
  change (ringTransportExact e).smallKMap.{u + 1} 2
    (((ModuleCat.finiteModuleExactStructure.{u, u} A).smallKUniverseEquiv.{u, u + 1} 2)
      (((ModuleCat.finiteModuleExactStructure.{u, u} A).smallKUniverseEquiv.{u, u + 1} 2).symm
        (DvrSymbols.upperUnitProduct A a b))) = _
  rw [MulEquiv.apply_symm_apply, upperUnitProduct_ringIso]

end RingIsomorphism

section LocalDvr
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local notation "A" => Localization.AtPrime p.asIdeal
local notation "K₀" => FractionRing (Localization.AtPrime p.asIdeal)
local notation "κ" => p.asIdeal.ResidueField
local instance : IsDiscreteValuationRing A :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

/-- Reduction of the actual local-ring unit along its original residue map. -/
def residueUnit (a : Aˣ) : κˣ := Units.map (IsLocalRing.residue A).toMonoidHom a

variable {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)
include hπ

/-- The nonzero original uniformizer image in the actual canonical fraction field. -/
def fractionUniformizerUnit : K₀ˣ :=
  Units.mk0 (algebraMap A K₀ π) (by
    intro h
    apply hπ.ne_zero
    exact (IsFractionRing.injective A K₀) (h.trans (map_zero (algebraMap A K₀)).symm))

/-- The canonical fraction-field unit retains exactly the original image of π. -/
@[simp] theorem fractionUniformizerUnit_val :
    (fractionUniformizerUnit R p hπ : K₀) = algebraMap A K₀ π := rfl

private theorem fraction_coefficient (a : Aˣ) :
    Units.map (DedekindLocalDvr.principalAwayFractionEquiv R p hπ).toRingHom.toMonoidHom
        (Units.map (algebraMap A (Localization.Away π)).toMonoidHom a) =
      Units.map (algebraMap A K₀).toMonoidHom a := by
  apply Units.ext
  exact (DedekindLocalDvr.principalAwayFractionEquiv R p hπ).commutes (a : A)

private theorem fraction_uniformizer :
    Units.map (DedekindLocalDvr.principalAwayFractionEquiv R p hπ).toRingHom.toMonoidHom
        (FGModuleCat.PrincipalRankOne.localizationUnit A π) =
      fractionUniformizerUnit R p hπ := by
  apply Units.ext
  change (DedekindLocalDvr.principalAwayFractionEquiv R p hπ)
    (FGModuleCat.PrincipalRankOne.localizationUnit A π : Localization.Away π) =
      algebraMap A K₀ π
  rw [FGModuleCat.PrincipalRankOne.localizationUnit_val]
  exact (DedekindLocalDvr.principalAwayFractionEquiv R p hπ).commutes π

private theorem residue_coefficient (a : Aˣ) :
    Units.map (DedekindLocalDvr.principalClosedResidueEquiv R p hπ).toMonoidHom
        (PrincipalUnitBoundary.quotientUnit A π a) = residueUnit R p a := by
  exact Units.ext (Ideal.quotEquivOfEq_mk hπ.maximalIdeal_eq.symm (a : A))

/-- The original local-DVR boundary of the ordered actual field product of a
local unit and the uniformizer image is the literal positive native residue cube. -/
theorem localDvrBoundary_unit_principal (a : Aˣ) :
    DedekindLocalDvr.localDvrBoundary R p 1
        (((ModuleCat.finiteModuleExactStructure.{u, u} K₀).smallKUniverseEquiv.{u, u + 1} 2).symm
          (FieldSymbols.unitProduct K₀ (Units.map (algebraMap A K₀).toMonoidHom a)
            (fractionUniformizerUnit R p hπ))) =
      PrincipalUnitBoundary.rankOnePositiveCube κ (residueUnit R p a) := by
  let z := DvrSymbols.loweredUnitProduct (Localization.Away π)
    (Units.map (algebraMap A (Localization.Away π)).toMonoidHom a)
    (FGModuleCat.PrincipalRankOne.localizationUnit A π)
  have h := DFunLike.congr_fun (DedekindLocalDvr.principalBoundary_nativeBoundary R p hπ 1) z
  change (DedekindLocalDvr.principalResidueRestrictionExact R p hπ).smallKMap 1
      (closedConnectingHom π 1 z) =
    DedekindLocalDvr.localDvrBoundary R p 1
      ((DedekindLocalDvr.principalFractionRestrictionExact R p hπ).smallKMap 2 z) at h
  have hp : closedConnectingHom π 1 z = PrincipalUnitBoundary.rankOnePositiveCube
      (ClosedRing π) (PrincipalUnitBoundary.quotientUnit A π a) :=
    PrincipalUnitBoundary.closedConnectingHom_unit_principal A π
      (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero) a
  rw [hp] at h
  change (ringTransportExact (DedekindLocalDvr.principalClosedResidueEquiv R p hπ)).smallKMap 1
      (PrincipalUnitBoundary.rankOnePositiveCube (ClosedRing π)
        (PrincipalUnitBoundary.quotientUnit A π a)) =
    DedekindLocalDvr.localDvrBoundary R p 1
      ((ringTransportExact
        (DedekindLocalDvr.principalAwayFractionEquiv R p hπ).toRingEquiv).smallKMap 2 z) at h
  rw [rankOnePositiveCube_ringIso, residue_coefficient] at h
  dsimp only [z] at h
  rw [loweredUnitProduct_ringIso, fraction_coefficient, fraction_uniformizer,
    DvrSymbols.loweredUnitProduct_field] at h
  exact h.symm

/-- The original residue determinant is applied after canonical promotion of
the proved positive lower residue cube, giving the positive actual reduced unit. -/
theorem localDvrBoundary_unit_principal_det (a : Aˣ) :
    Field.moduleDetEquiv κ
        ((ModuleCat.finiteModuleExactStructure.{u, u} κ).smallKUniverseEquiv.{u, u + 1} 1
          (DedekindLocalDvr.localDvrBoundary R p 1
            (((ModuleCat.finiteModuleExactStructure.{u, u} K₀).smallKUniverseEquiv.{u, u + 1}
              2).symm (FieldSymbols.unitProduct K₀
                (Units.map (algebraMap A K₀).toMonoidHom a)
                (fractionUniformizerUnit R p hπ))))) = residueUnit R p a := by
  rw [localDvrBoundary_unit_principal]
  unfold PrincipalUnitBoundary.rankOnePositiveCube
  rw [UniverseNaturality.finiteModule_positiveScalarCube_universe,
    Field.moduleDetEquiv_matrix_cube, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin, pow_one]

section GivenFractionField
variable (K : Type u) [Field K] [Algebra (Localization.AtPrime p.asIdeal) K]
  [IsFractionRing (Localization.AtPrime p.asIdeal) K]

/-- The nonzero original uniformizer image in the supplied actual fraction field. -/
def givenUniformizerUnit : Kˣ :=
  Units.mk0 (algebraMap A K π) (by
    intro h
    apply hπ.ne_zero
    exact (IsFractionRing.injective A K) (h.trans (map_zero (algebraMap A K)).symm))

omit [IsDedekindDomain R] in
/-- The supplied fraction-field unit retains exactly its original algebra map. -/
@[simp] theorem givenUniformizerUnit_val :
    (givenUniformizerUnit R p hπ K : K) = algebraMap A K π := rfl

omit hπ in
/-- The actual restriction map used by the original supplied-field native
boundary comparison, along the canonical fraction-field equivalence. -/
def fractionFieldRestrictionExact :
    ExactFunctor (ModuleCat.finiteModuleExactStructure.{u, u} K)
      (ModuleCat.finiteModuleExactStructure.{u, u} K₀) :=
  ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact
    (CommRingCat.ofHom (DedekindLocalDvr.localFractionFieldEquiv R p K).toRingHom)
    (RingHom.Finite.of_surjective _ (DedekindLocalDvr.localFractionFieldEquiv R p K).surjective)

omit hπ [IsDedekindDomain R] in
private theorem given_coefficient (a : Aˣ) :
    Units.map (DedekindLocalDvr.localFractionFieldEquiv R p K).toRingEquiv.symm.toMonoidHom
        (Units.map (algebraMap A K).toMonoidHom a) =
      Units.map (algebraMap A K₀).toMonoidHom a := by
  apply Units.ext
  exact (DedekindLocalDvr.localFractionFieldEquiv R p K).symm.commutes (a : A)

private theorem given_uniformizer :
    Units.map (DedekindLocalDvr.localFractionFieldEquiv R p K).toRingEquiv.symm.toMonoidHom
        (givenUniformizerUnit R p hπ K) = fractionUniformizerUnit R p hπ := by
  apply Units.ext
  exact (DedekindLocalDvr.localFractionFieldEquiv R p K).symm.commutes π

/-- For a supplied actual fraction field, the original native local-DVR
boundary after its original canonical inverse field restriction has the same
positive native residue scalar-cube value, in the literal ordered inputs. -/
theorem localDvrBoundary_unit_principal_field (a : Aˣ) :
    DedekindLocalDvr.localDvrBoundary R p 1
        ((fractionFieldRestrictionExact R p K).smallKMap.{u} 2
          (((ModuleCat.finiteModuleExactStructure.{u, u} K).smallKUniverseEquiv.{u, u + 1}
            2).symm (FieldSymbols.unitProduct K (Units.map (algebraMap A K).toMonoidHom a)
              (givenUniformizerUnit R p hπ K)))) =
      PrincipalUnitBoundary.rankOnePositiveCube κ (residueUnit R p a) := by
  rw [← DvrSymbols.loweredUnitProduct_field]
  change DedekindLocalDvr.localDvrBoundary R p 1
    ((ringTransportExact
      (DedekindLocalDvr.localFractionFieldEquiv R p K).toRingEquiv.symm).smallKMap.{u} 2
        (DvrSymbols.loweredUnitProduct K _ _)) = _
  rw [loweredUnitProduct_ringIso, given_coefficient, given_uniformizer,
    DvrSymbols.loweredUnitProduct_field]
  exact localDvrBoundary_unit_principal R p hπ a

/-- The original residue determinant, after canonical promotion of the proved
supplied-field boundary value, is the positive actual reduced local-ring unit. -/
theorem localDvrBoundary_unit_principal_field_det (a : Aˣ) :
    Field.moduleDetEquiv κ
        ((ModuleCat.finiteModuleExactStructure.{u, u} κ).smallKUniverseEquiv.{u, u + 1} 1
          (DedekindLocalDvr.localDvrBoundary R p 1
            ((fractionFieldRestrictionExact R p K).smallKMap.{u} 2
              (((ModuleCat.finiteModuleExactStructure.{u, u} K).smallKUniverseEquiv.{u, u + 1}
                2).symm (FieldSymbols.unitProduct K
                  (Units.map (algebraMap A K).toMonoidHom a)
                  (givenUniformizerUnit R p hπ K)))))) = residueUnit R p a := by
  rw [localDvrBoundary_unit_principal_field]
  unfold PrincipalUnitBoundary.rankOnePositiveCube
  rw [UniverseNaturality.finiteModule_positiveScalarCube_universe,
    Field.moduleDetEquiv_matrix_cube, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin, pow_one]

end GivenFractionField

end LocalDvr

end Quillen.LowDegreeScalarAction.DvrUnitBoundary
