/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.FieldSymbols
public import Quillen.KTheory.Map.SmallModelUniverse
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Quillen.KTheory.GrothendieckComparison.Naturality
public import Quillen.GTheory.FiniteModules.LocalizationSequence
public import Quillen.GTheory.Dedekind.LocalDvrSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.ClosedDevissage

/-!
# Unit products and original localization boundaries

The inverse scalar operation on a free rank-one object supplies the positive
unit K1 class over a noetherian commutative ring. Over a field it is exactly the
class calibrated by the original upper determinant and positive matrix cube.
The original scalar K1-to-K2 action then gives a ring-unit product whose actual
localization image is the same product of localized units.

The canonical comparison of universes of the same chosen finite-module model
carries this upper product to the original lower localization sequence. Actual
exactness proves its boundary is the identity. The lower product is explicitly
defined by this canonical comparison; no equality of the two group objects or
unproved compatibility of their scalar operations is used.

Only unit-unit boundary zero is proved here. The Steinberg relation and
identification with `StableSteinberg.milnorToKernel` or a marked Milnor-to-Quillen
comparison remain open. No unit-uniformizer boundary formula is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open scoped ZeroObject ModuleCat.Algebra

namespace Quillen.LowDegreeScalarAction.DvrSymbols

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The original upper object class of the free module with Fin 1 coordinates. -/
def upperRankOneClass :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).SmallK.{u + 1} 0 :=
  (ModuleCat.finiteModuleExactStructure.{u, u} R).smallModel.{u + 1}.kZeroObjectClass
    ((equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor.obj
      (FGModuleCat.of R (Fin 1 → R)))

/-- The positive upper unit K1 class, retaining the original scalar-action inverse. -/
def upperUnitKOne (b : Rˣ) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).SmallK.{u + 1} 1 :=
  (ScalarUnit.upperFiniteModuleKZeroAction R b (upperRankOneClass R))⁻¹

/-- The original upper scalar action applied to the positive ring-unit K1 class. -/
def upperUnitProduct (a b : Rˣ) :
    (ModuleCat.finiteModuleExactStructure.{u, u} R).SmallK.{u + 1} 2 :=
  ScalarUnit.upperFiniteModuleKOneAction R a (upperUnitKOne R b)

/-- The canonical comparison, on the same actual finite-module category, places
the upper product in the original lower localization-sequence group. -/
def loweredUnitProduct (a b : Rˣ) : FiniteModuleLocalization.G R 2 :=
  ((ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 2).symm
    (upperUnitProduct R a b)

section Fields
variable (F : Type u) [Field F]

/-- Over a field, the ring construction uses exactly the original determinant
inverse with its proved positive matrix-cube calibration. -/
theorem upperUnitKOne_field (b : Fˣ) :
    upperUnitKOne F b = FieldSymbols.positiveUnitKOne F b :=
  (FieldSymbols.positiveUnitKOne_inverse_scalarObjectClass F b).symm

/-- The upper ring-unit product is the original ordered field product. -/
theorem upperUnitProduct_field (a b : Fˣ) :
    upperUnitProduct F a b = FieldSymbols.unitProduct F a b := by
  unfold upperUnitProduct FieldSymbols.unitProduct
  rw [upperUnitKOne_field]

/-- The lower boundary input is the canonical universe transport of the
original upper field product. -/
theorem loweredUnitProduct_field (a b : Fˣ) :
    loweredUnitProduct F a b =
      ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1} 2).symm
        (FieldSymbols.unitProduct F a b) := by
  unfold loweredUnitProduct
  rw [upperUnitProduct_field]

end Fields

variable (S : Submonoid R)

omit [IsNoetherianRing R] in
private theorem localization_linear :
    (ModuleCat.FiniteLocalization.functor S).Linear R where
  map_smul {M N} f r := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    ext z
    change IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
        (N.obj.localizedModuleMkLinearMap S) (Localization S) (r • f.hom.hom) z =
      (algebraMap R (Localization S) r) •
        IsLocalizedModule.mapExtendScalars S (M.obj.localizedModuleMkLinearMap S)
          (N.obj.localizedModuleMkLinearMap S) (Localization S) f.hom.hom z
    rw [map_smul, LinearMap.smul_apply, algebraMap_smul]

omit [IsNoetherianRing R] in
private theorem localized_scalar (a : Rˣ) :
    smallModelScalarNatAut.{u, u + 1, u, u + 1} R (FGModuleCat.{u} (Localization S)) a =
      smallModelScalarNatAut.{u, u + 1, u, u + 1} (Localization S)
        (FGModuleCat.{u} (Localization S))
        (Units.map (algebraMap R (Localization S)).toMonoidHom a) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (equivSmallModel.{u + 1} (FGModuleCat.{u} (Localization S))).inverse.map_injective
  rw [smallModelScalarNatAut_map_hom, smallModelScalarNatAut_map_hom]
  rfl

private def rankOneCoordinates : (Fin 1 → R) →ₗ[R] (Fin 1 → Localization S) :=
  LinearMap.pi fun i => (Algebra.linearMap R (Localization S)).comp (LinearMap.proj i)

omit [IsNoetherianRing R] in
private theorem rankOneCoordinates_isLocalizedModule :
    IsLocalizedModule S (rankOneCoordinates R S) := by
  dsimp only [rankOneCoordinates]
  infer_instance

attribute [local instance] rankOneCoordinates_isLocalizedModule

private def localizedRankOneIso :
    (ModuleCat.FiniteLocalization.functor S).obj (FGModuleCat.of R (Fin 1 → R)) ≅
      FGModuleCat.of (Localization S) (Fin 1 → Localization S) := by
  let M := (FGModuleCat.of R (Fin 1 → R)).obj
  letI := ModuleCat.localizedModule_isLocalizedModule M S
  exact ObjectProperty.isoMk _
    ((IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
      (rankOneCoordinates R S)).extendScalarsOfIsLocalization S (Localization S)).toModuleIso

private theorem localizedRankOneClass :
    (FiniteModuleLocalization.exactFunctor S).smallKMap.{u + 1} 0 (upperRankOneClass R) =
      upperRankOneClass (Localization S) := by
  unfold upperRankOneClass
  change (FiniteModuleLocalization.exactFunctor S).smallModel.{u + 1}.KMap 0 _ = _
  rw [ExactFunctor.KMap_kZeroObjectClass]
  apply ExactStructure.kZeroObjectClass_iso
  exact (equivSmallModel.{u + 1} (FGModuleCat.{u} (Localization S))).functor.mapIso
    (((FiniteModuleLocalization.exactFunctor S).toFunctor.mapIso
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} R)).unitIso.app
        (FGModuleCat.of R (Fin 1 → R))).symm) ≪≫ localizedRankOneIso R S)

/-- Actual scalar localization preserves the original upper positive unit class. -/
theorem upperUnitKOne_localization (b : Rˣ) :
    (FiniteModuleLocalization.exactFunctor S).smallKMap.{u + 1} 1 (upperUnitKOne R b) =
      upperUnitKOne (Localization S)
        (Units.map (algebraMap R (Localization S)).toMonoidHom b) := by
  let : (FiniteModuleLocalization.exactFunctor S).toFunctor.Linear R := localization_linear R S
  unfold upperUnitKOne ScalarUnit.upperFiniteModuleKZeroAction
  rw [map_inv, ScalarUnit.smallModelKZeroAction_natural, localizedRankOneClass]
  rw [ScalarUnit.smallModelKZeroAction_apply, ScalarUnit.smallModelKZeroAction_apply,
    localized_scalar]

/-- Actual localization preserves the original upper ring-unit product. -/
theorem upperUnitProduct_localization (a b : Rˣ) :
    (FiniteModuleLocalization.exactFunctor S).smallKMap.{u + 1} 2 (upperUnitProduct R a b) =
      upperUnitProduct (Localization S)
        (Units.map (algebraMap R (Localization S)).toMonoidHom a)
        (Units.map (algebraMap R (Localization S)).toMonoidHom b) := by
  let : (FiniteModuleLocalization.exactFunctor S).toFunctor.Linear R := localization_linear R S
  unfold upperUnitProduct ScalarUnit.upperFiniteModuleKOneAction
  rw [ScalarUnit.smallModelKOneAction_natural]
  rw [ScalarUnit.smallModelKOneAction_apply, ScalarUnit.smallModelKOneAction_apply,
    localized_scalar, upperUnitKOne_localization]

/-- The actual lower localization map preserves the product transported through
the canonical universes of the same finite-module category. -/
theorem loweredUnitProduct_localization (a b : Rˣ) :
    FiniteModuleLocalization.localizationKMap S 2 (loweredUnitProduct R a b) =
      loweredUnitProduct (Localization S)
        (Units.map (algebraMap R (Localization S)).toMonoidHom a)
        (Units.map (algebraMap R (Localization S)).toMonoidHom b) := by
  apply ((ModuleCat.finiteModuleExactStructure.{u, u}
    (Localization S)).smallKUniverseEquiv.{u, u + 1} 2).injective
  have h := DFunLike.congr_fun
    (ExactFunctor.smallKUniverseEquiv_naturality.{u, u + 1}
      (FiniteModuleLocalization.exactFunctor S) 2) (loweredUnitProduct R a b)
  change (FiniteModuleLocalization.exactFunctor S).smallKMap.{u + 1} 2
      (((ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 2)
        (loweredUnitProduct R a b)) =
    ((ModuleCat.finiteModuleExactStructure.{u, u} (Localization S)).smallKUniverseEquiv.{u, u + 1}
      2) (FiniteModuleLocalization.localizationKMap S 2 (loweredUnitProduct R a b)) at h
  rw [show ((ModuleCat.finiteModuleExactStructure.{u, u}
      (Localization S)).smallKUniverseEquiv.{u, u + 1} 2)
        (loweredUnitProduct (Localization S) _ _) =
          upperUnitProduct (Localization S) _ _ from
    MulEquiv.apply_symm_apply _ _]
  rw [← h]
  change (FiniteModuleLocalization.exactFunctor S).smallKMap.{u + 1} 2
    (((ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 2)
      (((ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 2).symm
        (upperUnitProduct R a b))) = _
  rw [MulEquiv.apply_symm_apply, upperUnitProduct_localization]

/-- A pair of ring units has identity under the original localization boundary. -/
theorem connectingHom_unit_unit (a b : Rˣ) :
    FiniteModuleLocalization.connectingHom S 1
      (loweredUnitProduct (Localization S)
        (Units.map (algebraMap R (Localization S)).toMonoidHom a)
        (Units.map (algebraMap R (Localization S)).toMonoidHom b)) = 1 := by
  have h : FiniteModuleLocalization.localizationKMap S 2 (loweredUnitProduct R a b) ∈
      (FiniteModuleLocalization.connectingHom S 1).ker := by
    rw [← FiniteModuleLocalization.localization_range_eq_connecting_ker]
    exact ⟨loweredUnitProduct R a b, rfl⟩
  rw [loweredUnitProduct_localization] at h
  exact h

/-- The actual principal closed boundary also vanishes on pairs of ring units. -/
theorem closedConnectingHom_unit_unit (r : R) (a b : Rˣ) :
    FiniteModuleLocalization.closedConnectingHom r 1
      (loweredUnitProduct (Localization.Away r)
        (Units.map (algebraMap R (Localization.Away r)).toMonoidHom a)
        (Units.map (algebraMap R (Localization.Away r)).toMonoidHom b)) = 1 := by
  change (FiniteModuleLocalization.closedSupportGEquiv r 1).symm
    (FiniteModuleLocalization.connectingHom (Submonoid.powers r) 1 _) = 1
  rw [connectingHom_unit_unit, map_one]

open scoped nonZeroDivisors in
/-- On the fraction field of a noetherian domain, the original boundary of the
canonically lowered original field product of two ring units is the identity. -/
theorem fractionConnectingHom_unit_unit [IsDomain R] (a b : Rˣ) :
    FiniteModuleLocalization.connectingHom R⁰ 1
      (((ModuleCat.finiteModuleExactStructure.{u, u}
        (FractionRing R)).smallKUniverseEquiv.{u, u + 1} 2).symm
          (FieldSymbols.unitProduct (FractionRing R)
            (Units.map (algebraMap R (FractionRing R)).toMonoidHom a)
            (Units.map (algebraMap R (FractionRing R)).toMonoidHom b))) = 1 := by
  rw [← loweredUnitProduct_field]
  exact connectingHom_unit_unit R R⁰ a b

section LocalDvr
variable (A : Type u) [CommRing A] [IsDedekindDomain A]
  (p : IsDedekindDomain.HeightOneSpectrum A)

/-- The original local-DVR residue boundary vanishes on the canonically
transported original field product of any two units of the actual local ring. -/
theorem localDvrBoundary_unit_unit (a b : (Localization.AtPrime p.asIdeal)ˣ) :
    DedekindLocalDvr.localDvrBoundary A p 1
      (((ModuleCat.finiteModuleExactStructure.{u, u}
        (FractionRing (Localization.AtPrime p.asIdeal))).smallKUniverseEquiv.{u, u + 1} 2).symm
          (FieldSymbols.unitProduct (FractionRing (Localization.AtPrime p.asIdeal))
            (Units.map (algebraMap (Localization.AtPrime p.asIdeal)
              (FractionRing (Localization.AtPrime p.asIdeal))).toMonoidHom a)
            (Units.map (algebraMap (Localization.AtPrime p.asIdeal)
              (FractionRing (Localization.AtPrime p.asIdeal))).toMonoidHom b))) = 1 := by
  change (DedekindLocalDvr.localResidueSupportKEquiv A p 1).symm
    (FiniteModuleLocalization.connectingHom _ 1 _) = 1
  rw [fractionConnectingHom_unit_unit, map_one]

end LocalDvr

end Quillen.LowDegreeScalarAction.DvrSymbols
