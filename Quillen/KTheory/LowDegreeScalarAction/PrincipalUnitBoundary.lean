/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.UniverseNaturality
public import Quillen.KTheory.LowDegreeScalarAction.DvrSymbols
public import Quillen.KTheory.LowDegreeScalarAction.SmallModelBoundary
public import Quillen.GTheory.FiniteModules.PrincipalObjectBoundary

/-!
# The original principal boundary of a unit and the inverted principal element

The canonical lower image of the existing upper unit product is the original
lower scalar operation on the literal positive rank-one scalar cube. Actual
quotient restriction gives the closed-to-supported scalar square. The signed
boundary formula and the positive principal object calibration therefore yield
the positive quotient scalar cube: the boundary inverse and the object-class
normalization inverse cancel explicitly.

The coefficient ring is only assumed commutative and noetherian, and the
principal element is regular. No field, residue-cardinality, Steinberg relation,
Milnor comparison or marked K2 identification is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open Quillen.FiniteModuleLocalization
open scoped ZeroObject ModuleCat.Algebra nonZeroDivisors

namespace Quillen.LowDegreeScalarAction.PrincipalUnitBoundary

variable (R : Type u) [CommRing R] [IsNoetherianRing R]

/-- The literal original lower-model positive cube of a rank-one scalar matrix. -/
def rankOnePositiveCube (a : Rˣ) : FiniteModuleLocalization.G R 1 :=
  Quotient.mk' (Automorphism.Cube.automorphismFirstCube
    (ModuleCat.finiteModuleExactStructure.{u, u} R).smallModel.{u}
    ((equivSmallModel.{u} (FGModuleCat.{u} R)).functor.obj
      (FGModuleCat.of R (Fin 1 → R)))
    ((equivSmallModel.{u} (FGModuleCat.{u} R)).functor.mapIso
      (FGModuleCat.matrixToAut R 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a))))

/-- The original lower-model object class of the same rank-one free module. -/
def rankOneObjectClass : FiniteModuleLocalization.G R 0 :=
  (ModuleCat.finiteModuleExactStructure.{u, u} R).smallModel.{u}.kZeroObjectClass
    (FiniteModuleLocalization.PrincipalObjectBoundary.smallRankOne R)

omit [IsNoetherianRing R] in
private theorem scalarMatrixAut (a : Rˣ) :
    (scalarNatAut R (FGModuleCat.{u} R) a).app (FGModuleCat.of R (Fin 1 → R)) =
      FGModuleCat.matrixToAut R 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a) := by
  apply Iso.ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((scalarNatAut R (FGModuleCat.{u} R) a).hom.app
    (FGModuleCat.of R (Fin 1 → R))) x =
    (FGModuleCat.matrixToAut R 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) a)).hom x
  rw [FGModuleCat.matrixToAut_apply]
  change (fun i : Fin 1 => (a : R) * x i) = (Matrix.scalar (Fin 1) (a : R)).mulVec x
  funext i
  simp only [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- The original rank-one scalar K0 action is inverse to its positive cube. -/
theorem rankOneObjectClass_scalar (a : Rˣ) :
    ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u} R
        (ModuleCat.finiteModuleExactStructure.{u, u} R) a (rankOneObjectClass R) =
      (rankOnePositiveCube R a)⁻¹ := by
  simpa only [scalarMatrixAut, rankOneObjectClass, rankOnePositiveCube] using
    (ObjectClass.smallModelKZeroAction_mapped_objectClass_cube.{u + 1, u, u, u} R
      (ModuleCat.finiteModuleExactStructure.{u, u} R) a (FGModuleCat.of R (Fin 1 → R)))

/-- The generic ring's original upper positive unit class is the canonical
promotion of its literal original lower positive rank-one matrix cube. -/
theorem upperUnitKOne_eq_promotedCube (b : Rˣ) :
    DvrSymbols.upperUnitKOne R b =
      (ModuleCat.finiteModuleExactStructure.{u, u} R).smallKUniverseEquiv.{u, u + 1} 1
        (rankOnePositiveCube R b) := by
  unfold rankOnePositiveCube
  rw [UniverseNaturality.finiteModule_positiveScalarCube_universe]
  have h := ObjectClass.smallModelKZeroAction_mapped_objectClass_cube.{u + 1, u, u, u + 1}
    R (ModuleCat.finiteModuleExactStructure.{u, u} R) b (FGModuleCat.of R (Fin 1 → R))
  rw [scalarMatrixAut] at h
  simpa only [DvrSymbols.upperUnitKOne, DvrSymbols.upperRankOneClass,
    ScalarUnit.upperFiniteModuleKZeroAction, inv_inv] using congrArg Inv.inv h

/-- The original lower ring-unit product is the original lower scalar action
on its literal positive rank-one scalar matrix cube. -/
theorem loweredUnitProduct_eq_scalarCubeAction (a b : Rˣ) :
    DvrSymbols.loweredUnitProduct R a b =
      ScalarUnit.smallModelKOneAction.{u, u + 1, u, u} R
        (ModuleCat.finiteModuleExactStructure.{u, u} R) a (rankOnePositiveCube R b) := by
  apply ((ModuleCat.finiteModuleExactStructure.{u, u}
    R).smallKUniverseEquiv.{u, u + 1} 2).injective
  rw [DvrSymbols.loweredUnitProduct, MulEquiv.apply_symm_apply,
    UniverseNaturality.finiteModule_kOneAction_universe]
  unfold DvrSymbols.upperUnitProduct
  rw [upperUnitKOne_eq_promotedCube]

variable (r : R)

/-- The original quotient map, applied to an actual unit of the original ring. -/
def quotientUnit (a : Rˣ) : (ClosedRing r)ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom a

omit [IsNoetherianRing R] in
private theorem closedRestriction_scalar (a : Rˣ) (M : FGModuleCat.{u} (ClosedRing r)) :
    (closedRestriction r).map
        ((scalarNatAut (ClosedRing r) (FGModuleCat.{u} (ClosedRing r))
          (quotientUnit R r a)).hom.app M) =
      (scalarNatAut R (FGModuleCat.{u} R) a).hom.app ((closedRestriction r).obj M) := by
  apply FGModuleCat.hom_ext
  rfl

private theorem smallClosedRestriction_scalar (a : Rˣ)
    (X : SmallModel.{u} (FGModuleCat.{u} (ClosedRing r))) :
    (closedRestrictionExact r).smallModel.{u}.toFunctor.map
        ((smallModelScalarNatAut.{u, u + 1, u, u} (ClosedRing r)
          (FGModuleCat.{u} (ClosedRing r)) (quotientUnit R r a)).hom.app X) =
      (smallModelScalarNatAut.{u, u + 1, u, u} R (FGModuleCat.{u} R) a).hom.app
        ((closedRestrictionExact r).smallModel.{u}.toFunctor.obj X) := by
  change (equivSmallModel.{u} (FGModuleCat.{u} R)).functor.map
    ((closedRestriction r).map
      ((equivSmallModel.{u} (FGModuleCat.{u} (ClosedRing r))).inverse.map
        ((smallModelScalarNatAut.{u, u + 1, u, u} (ClosedRing r)
          (FGModuleCat.{u} (ClosedRing r)) (quotientUnit R r a)).hom.app X))) = _
  rw [smallModelScalarNatAut_map_hom]
  change (equivSmallModel.{u} (FGModuleCat.{u} R)).functor.map
    ((closedRestriction r).map
      ((scalarNatAut (ClosedRing r) (FGModuleCat.{u} (ClosedRing r))
        (quotientUnit R r a)).hom.app
          ((equivSmallModel.{u} (FGModuleCat.{u} (ClosedRing r))).inverse.obj X))) = _
  rw [closedRestriction_scalar]
  exact smallModelScalarNatAut_functor_map_hom.{u, u + 1, u, u} R (FGModuleCat.{u} R) a _

/-- The actual closed-to-support functor preserves the descended quotient
scalar and the actual restricted original scalar, component by component. -/
theorem smallClosedToSupport_scalar (a : Rˣ)
    (X : SmallModel.{u} (FGModuleCat.{u} (ClosedRing r))) :
    (smallClosedToSupportExact r).toFunctor.map
        ((smallModelScalarNatAut.{u, u + 1, u, u} (ClosedRing r)
          (FGModuleCat.{u} (ClosedRing r)) (quotientUnit R r a)).hom.app X) =
      (SerreBoundary.restrictedNatAut (smallTorsion (Submonoid.powers r))
        (smallModelScalarNatAut.{u, u + 1, u, u} R (FGModuleCat.{u} R) a)).hom.app
        ((smallClosedToSupportExact r).toFunctor.obj X) := by
  apply ObjectProperty.hom_ext
  exact smallClosedRestriction_scalar R r a X

/-- The original closed-support equivalence intertwines the actual quotient
scalar K0 action and the actual supported original-ring scalar K0 action. -/
theorem closedSupportGEquiv_scalar (a : Rˣ) (z : FiniteModuleLocalization.G (ClosedRing r) 0) :
    closedSupportGEquiv r 1
        (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u} (ClosedRing r)
          (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)) (quotientUnit R r a) z) =
      SmallModelBoundary.finiteSupportedKZeroAction (Submonoid.powers r) a
        (closedSupportGEquiv r 0 z) := by
  have h := ExactNaturality.kZeroAction_natural.{u, u} (smallClosedToSupportExact r)
    (smallModelScalarNatAut.{u, u + 1, u, u} (ClosedRing r)
      (FGModuleCat.{u} (ClosedRing r)) (quotientUnit R r a))
    (SerreBoundary.restrictedNatAut (smallTorsion (Submonoid.powers r))
      (smallModelScalarNatAut.{u, u + 1, u, u} R (FGModuleCat.{u} R) a))
    (smallClosedToSupport_scalar R r a) z
  have h₁ := DFunLike.congr_fun (closedSupportGEquiv_coe r 1)
    (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u} (ClosedRing r)
      (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)) (quotientUnit R r a) z)
  have h₀ := DFunLike.congr_fun (closedSupportGEquiv_coe r 0) z
  exact h₁.trans (h.trans (congrArg
    (SmallModelBoundary.finiteSupportedKZeroAction (Submonoid.powers r) a) h₀.symm))

/-- The original principal closed boundary has the inverse signed scalar
formula, with its original quotient-ring action and actual closed-support map. -/
theorem closedConnectingHom_scalar (a : Rˣ)
    (z : FiniteModuleLocalization.G (Localization.Away r) 1) :
    closedConnectingHom r 1
        (ScalarUnit.smallModelKOneAction.{u, u + 1, u, u} R
          (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)) a z) =
      (ScalarUnit.smallModelKZeroAction.{u, u + 1, u, u} (ClosedRing r)
        (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)) (quotientUnit R r a)
        (closedConnectingHom r 0 z))⁻¹ := by
  apply (closedSupportGEquiv r 1).injective
  change closedSupportGEquiv r 1 ((closedSupportGEquiv r 1).symm _) = _
  rw [MulEquiv.apply_symm_apply, map_inv, closedSupportGEquiv_scalar]
  change connectingHom (Submonoid.powers r) 1 _ =
    (SmallModelBoundary.finiteSupportedKZeroAction (Submonoid.powers r) a
      (closedSupportGEquiv r 0 ((closedSupportGEquiv r 0).symm _)))⁻¹
  rw [MulEquiv.apply_symm_apply]
  exact SmallModelBoundary.finiteConnectingHom_scalar (Submonoid.powers r) a z

omit [IsNoetherianRing R] in
private theorem localized_scalar (a : Rˣ) :
    smallModelScalarNatAut.{u, u + 1, u, u} R (FGModuleCat.{u} (Localization.Away r)) a =
      smallModelScalarNatAut.{u, u + 1, u, u} (Localization.Away r)
        (FGModuleCat.{u} (Localization.Away r))
        (Units.map (algebraMap R (Localization.Away r)).toMonoidHom a) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (equivSmallModel.{u} (FGModuleCat.{u} (Localization.Away r))).inverse.map_injective
  rw [smallModelScalarNatAut_map_hom, smallModelScalarNatAut_map_hom]
  rfl

/-- The original lower source is the original-ring scalar operation on the
literal invertible image of the principal element. -/
theorem principalProduct_eq_scalarCubeAction (a : Rˣ) :
    DvrSymbols.loweredUnitProduct (Localization.Away r)
        (Units.map (algebraMap R (Localization.Away r)).toMonoidHom a)
        (FGModuleCat.PrincipalRankOne.localizationUnit R r) =
      ScalarUnit.smallModelKOneAction.{u, u + 1, u, u} R
        (ModuleCat.finiteModuleExactStructure.{u, u} (Localization.Away r)) a
        (rankOnePositiveCube (Localization.Away r)
          (FGModuleCat.PrincipalRankOne.localizationUnit R r)) := by
  rw [loweredUnitProduct_eq_scalarCubeAction, ScalarUnit.smallModelKOneAction_apply,
    ScalarUnit.smallModelKOneAction_apply, localized_scalar]

/-- The positive principal calibration is the same literal cube and
the same original quotient rank-one object class used by the scalar action. -/
theorem closedConnectingHom_principalCube (hr : r ∈ nonZeroDivisors R) :
    closedConnectingHom r 0
        (rankOnePositiveCube (Localization.Away r)
          (FGModuleCat.PrincipalRankOne.localizationUnit R r)) =
      rankOneObjectClass (ClosedRing r) :=
  FiniteModuleLocalization.PrincipalObjectBoundary.closedConnectingHom_positiveRankOne R r hr

/-- The original principal closed boundary of the existing unit/r product is
the original positive quotient scalar cube. The two normalization inverses
are explicitly present before their cancellation. -/
theorem closedConnectingHom_unit_principal (hr : r ∈ nonZeroDivisors R) (a : Rˣ) :
    closedConnectingHom r 1
        (DvrSymbols.loweredUnitProduct (Localization.Away r)
          (Units.map (algebraMap R (Localization.Away r)).toMonoidHom a)
          (FGModuleCat.PrincipalRankOne.localizationUnit R r)) =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing r)).smallModel.{u}
        ((equivSmallModel.{u} (FGModuleCat.{u} (ClosedRing r))).functor.obj
          (FGModuleCat.of (ClosedRing r) (Fin 1 → ClosedRing r)))
        ((equivSmallModel.{u} (FGModuleCat.{u} (ClosedRing r))).functor.mapIso
          (FGModuleCat.matrixToAut (ClosedRing r) 1
            (Matrix.GeneralLinearGroup.scalar (Fin 1)
              (Units.map (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom a))))) :
                FiniteModuleLocalization.G (ClosedRing r) 1) := by
  change closedConnectingHom r 1 _ = rankOnePositiveCube (ClosedRing r) (quotientUnit R r a)
  rw [principalProduct_eq_scalarCubeAction, closedConnectingHom_scalar,
    closedConnectingHom_principalCube R r hr, rankOneObjectClass_scalar, inv_inv]

end Quillen.LowDegreeScalarAction.PrincipalUnitBoundary
