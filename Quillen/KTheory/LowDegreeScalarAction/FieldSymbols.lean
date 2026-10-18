/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.ObjectClass
public import Quillen.KTheory.Field.MatrixCubeComparison

/-!
# Positive unit products on the original upper field K-groups

The inverse of the original finite-module determinant is calibrated by the
literal positive rank-one matrix cube. Applying the original scalar K1-to-K2
operation defines a product of two field units. Both multiplicative laws and
field-extension naturality concern these original maps and group objects.

The Steinberg relation and identification with
`StableSteinberg.milnorToKernel` or a Milnor-to-Quillen comparison remain open.
The localization client proves unit-unit boundary zero for the canonical lower
image of this same upper product.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open scoped ZeroObject TensorProduct ChangeOfRings

namespace Quillen.LowDegreeScalarAction.FieldSymbols

variable (F : Type u) [Field F]

/-- The original upper K1 class with determinant equal to the prescribed unit. -/
def positiveUnitKOne : Fˣ →*
    (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1 :=
  (Field.moduleDetEquiv F).symm.toMonoidHom

/-- This determinant inverse is the literal positive rank-one matrix cube. -/
theorem positiveUnitKOne_cube (b : Fˣ) :
    positiveUnitKOne F b =
      (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
          (FGModuleCat.of F (Fin 1 → F)))
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
          (FGModuleCat.matrixToAut F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) b)))) :
            (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) := by
  apply (Field.moduleDetEquiv F).injective
  rw [positiveUnitKOne, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulEquiv.apply_symm_apply, Field.moduleDetEquiv_matrix_cube,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]

/-- The original scalar action on the rank-one object class is inverse to
the positive class used here. -/
theorem positiveUnitKOne_inverse_scalarObjectClass (b : Fˣ) :
    positiveUnitKOne F b =
      (ScalarUnit.upperFiniteModuleKZeroAction F b
        ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}.kZeroObjectClass
          ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
            (FGModuleCat.of F (Fin 1 → F)))))⁻¹ := by
  apply (Field.moduleDetEquiv F).injective
  rw [map_inv, ObjectClass.moduleDetEquiv_scalar_rankOne_objectClass, inv_inv]
  exact (Field.moduleDetEquiv F).apply_symm_apply b

/-- The original scalar operation applied to the positive rank-one K1 class.
Its bilinearity and field naturality are proved below; the Steinberg relation
and identification with the algebraic Steinberg-kernel map remain open. -/
def unitProduct (a b : Fˣ) :
    (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 2 :=
  ScalarUnit.upperFiniteModuleKOneAction F a (positiveUnitKOne F b)

/-- Multiplication in the first unit gives the original K2 product. -/
theorem unitProduct_mul_left (a b c : Fˣ) :
    unitProduct F (a * b) c = unitProduct F a c * unitProduct F b c :=
  DFunLike.congr_fun (ScalarUnit.upperFiniteModuleKOneAction F |>.map_mul a b)
    (positiveUnitKOne F c)

/-- Multiplication in the second unit gives the original K2 product. -/
theorem unitProduct_mul_right (a b c : Fˣ) :
    unitProduct F a (b * c) = unitProduct F a b * unitProduct F a c := by
  unfold unitProduct
  rw [map_mul, map_mul]

/-- The identity in the first unit gives the identity class. -/
@[simp] theorem unitProduct_one_left (b : Fˣ) : unitProduct F 1 b = 1 :=
  DFunLike.congr_fun (ScalarUnit.upperFiniteModuleKOneAction F).map_one
    (positiveUnitKOne F b)

/-- The identity in the second unit gives the identity class. -/
@[simp] theorem unitProduct_one_right (a : Fˣ) : unitProduct F a 1 = 1 := by
  unfold unitProduct
  rw [map_one, map_one]

variable {F} {L : Type u} [Field L] (f : F →+* L)

/-- Actual tensor extension carries the positive rank-one class to the same
positive class with the mapped scalar unit. -/
theorem positiveUnitKOne_natural (b : Fˣ) :
    (Field.finiteModuleExtensionExact f).smallKMap.{u + 1} 1 (positiveUnitKOne F b) =
      positiveUnitKOne L (Units.map f.toMonoidHom b) := by
  apply (Field.moduleDetEquiv L).injective
  rw [Field.moduleDetEquiv_scalarExtension]
  change (Units.map f.toMonoidHom) ((Field.moduleDetEquiv F) ((Field.moduleDetEquiv F).symm b)) =
    (Field.moduleDetEquiv L) ((Field.moduleDetEquiv L).symm ((Units.map f.toMonoidHom) b))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem extension_scalar (a : Fˣ) (M : FGModuleCat.{u} F) :
    (Field.finiteModuleExtension f).map ((scalarNatAut F (FGModuleCat.{u} F) a).hom.app M) =
      (scalarNatAut L (FGModuleCat.{u} L) (Units.map f.toMonoidHom a)).hom.app
        ((Field.finiteModuleExtension f).obj M) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : L) ⊗ₜ[F, f] ((a : F) • m) =
    (f (a : F)) • ((1 : L) ⊗ₜ[F, f] m)
  let := f.toAlgebra
  change (1 : L) ⊗ₜ[F] ((a : F) • m) =
    (f (a : F)) • ((1 : L) ⊗ₜ[F] m)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

private theorem extension_small_scalar (a : Fˣ) (X : SmallModel.{u + 1} (FGModuleCat.{u} F)) :
    (Field.finiteModuleExtensionExact f).smallModel.{u + 1}.toFunctor.map
        ((smallModelScalarNatAut.{u, u + 1, u, u + 1} F
          (FGModuleCat.{u} F) a).hom.app X) =
      (smallModelScalarNatAut.{u, u + 1, u, u + 1} L (FGModuleCat.{u} L)
        (Units.map f.toMonoidHom a)).hom.app
        ((Field.finiteModuleExtensionExact f).smallModel.{u + 1}.toFunctor.obj X) := by
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} L)).functor.map
    ((Field.finiteModuleExtension f).map
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).inverse.map
        ((smallModelScalarNatAut.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a).hom.app X))) = _
  rw [smallModelScalarNatAut_map_hom]
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} L)).functor.map
    ((Field.finiteModuleExtension f).map
      ((scalarNatAut F (FGModuleCat.{u} F) a).hom.app
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).inverse.obj X))) = _
  rw [extension_scalar]
  exact smallModelScalarNatAut_functor_map_hom.{u, u + 1, u, u + 1} L (FGModuleCat.{u} L)
    (Units.map f.toMonoidHom a) _

/-- The actual scalar K1-to-K2 action commutes with literal tensor extension
and maps its original scalar coefficient by the same field homomorphism. -/
theorem scalarAction_natural (a : Fˣ)
    (z : (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) :
    (Field.finiteModuleExtensionExact f).smallKMap.{u + 1} 2
        (ScalarUnit.upperFiniteModuleKOneAction F a z) =
      ScalarUnit.upperFiniteModuleKOneAction L (Units.map f.toMonoidHom a)
        ((Field.finiteModuleExtensionExact f).smallKMap.{u + 1} 1 z) :=
  ExactNaturality.kOneAction_natural.{u + 1, u + 1}
    (Field.finiteModuleExtensionExact f).smallModel.{u + 1}
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a)
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} L (FGModuleCat.{u} L) (Units.map f.toMonoidHom a))
    (extension_small_scalar f a) z

/-- Literal field extension preserves the actual ordered product of units. -/
theorem unitProduct_natural (a b : Fˣ) :
    (Field.finiteModuleExtensionExact f).smallKMap.{u + 1} 2 (unitProduct F a b) =
      unitProduct L (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by
  unfold unitProduct
  rw [scalarAction_natural, positiveUnitKOne_natural]

end Quillen.LowDegreeScalarAction.FieldSymbols
