/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Field.ScalarExtensionComparison
public import Quillen.KTheory.Automorphism.Isomorphism
public import Quillen.CategoryTheory.GroupCompletion.StableFreeDiagram
public import Quillen.Aglib.Algebra.Category.FGModuleCat.ScalarMatrices

/-!
# The original stable matrix automorphism in finite-module coordinates

The native stable free sequence uses reversed finite bases. The explicit map
`x ↦ (i ↦ unop (x i.rev))` intertwines that action with the unchanged standard
matrix action. The original rank-one-power isomorphism and the actual upper
SmallModel functor retain this conjugacy. Consequently the two specified
transposed automorphism cubes have equal classes.

These are representative-transport equations. They do not identify the native
completion-to-Q class with either capped cube; that geometric comparison is
still required for determinant marking.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Field
variable (F : Type u) [Field F]

/-- Unopposition and the original basis reversal recover the standard left-module coordinates. -/
def freeModuleCoordinates (n : ℕ) :
    ((rightProjectiveToModuleExact F).toFunctor.obj
      (FiniteProjectiveModule.free (R := Fᵐᵒᵖ) n)) ≃ₗ[F] (Fin n → F) where
  toFun x i := MulOpposite.unop (x i.rev)
  invFun x i := MulOpposite.op (x i.rev)
  left_inv x := by
    change (fun i : Fin n => MulOpposite.op (MulOpposite.unop (x i.rev.rev))) = x
    simp
  right_inv x := by ext i; simp
  map_add' _ _ := rfl
  map_smul' r x := by
    ext i
    change MulOpposite.unop (x i.rev) * r = r * MulOpposite.unop (x i.rev)
    exact mul_comm _ _

/-- The explicit coordinate change is an isomorphism in the actual finite-module category. -/
def freeModuleCoordinatesIso (n : ℕ) :
    (rightProjectiveToModuleExact F).toFunctor.obj
      (FiniteProjectiveModule.free (R := Fᵐᵒᵖ) n) ≅ FGModuleCat.of F (Fin n → F) :=
  (freeModuleCoordinates F n).toFGModuleCatIso

/-- The transported reversed-basis action intertwines with the unchanged standard matrix action. -/
theorem freeModuleCoordinates_square (n : ℕ) (g : StableGeneralLinear.GL F n) :
    ((rightProjectiveToModuleExact F).toFunctor.mapIso
      (RightMatrix.leftFreeAutEquiv F n g)).hom ≫ (freeModuleCoordinatesIso F n).hom =
      (freeModuleCoordinatesIso F n).hom ≫ (FGModuleCat.matrixToAut F n g).hom := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (fun i => MulOpposite.unop ((RightMatrix.leftFreeAutEquiv F n g).hom.hom x i.rev)) =
    (FGModuleCat.matrixToAut F n g).hom (fun i => MulOpposite.unop (x i.rev))
  rw [FGModuleCat.matrixToAut_apply]
  funext i
  have h := congrArg (fun a : Aut (RightMatrix.freeModule F n) => a.hom x i.rev)
    (RightMatrix.leftFreeAutEquiv_map F n g)
  change (RightMatrix.leftFreeAutEquiv F n g).hom.hom x i.rev = _ at h
  rw [h, RightMatrix.leftModuleAutEquiv_apply, RightMatrix.moduleAutEquiv_hom_apply,
    Fin.rev_rev]
  rfl

/-- The same original finite automorphisms are conjugate by the specified coordinate
isomorphism. -/
theorem freeModuleCoordinates_conjugate (n : ℕ) (g : StableGeneralLinear.GL F n) :
    Aut.autMulEquivOfIso (freeModuleCoordinatesIso F n)
      ((rightProjectiveToModuleExact F).toFunctor.mapIso
        (RightMatrix.leftFreeAutEquiv F n g)) = FGModuleCat.matrixToAut F n g := by
  apply Iso.ext
  change (freeModuleCoordinatesIso F n).inv ≫
    (((rightProjectiveToModuleExact F).toFunctor.mapIso
      (RightMatrix.leftFreeAutEquiv F n g)).hom ≫ (freeModuleCoordinatesIso F n).hom) = _
  rw [freeModuleCoordinates_square]
  simp

/-- First apply the original power-to-free isomorphism, then the explicit matrix coordinates. -/
def powerModuleCoordinatesIso (n : ℕ) :
    (rightProjectiveToModuleExact F).toFunctor.obj
      (FiniteProjectiveModule.rankOnePower Fᵐᵒᵖ n).of ≅ FGModuleCat.of F (Fin n → F) :=
  (rightProjectiveToModuleExact F).toFunctor.mapIso
    (FiniteProjectiveModule.rankOnePowerIsoFree Fᵐᵒᵖ n).hom.iso ≪≫
      freeModuleCoordinatesIso F n

/-- The original rank-one-power automorphism has precisely the usual matrix action in these
coordinates. -/
theorem powerModuleCoordinates_square (n : ℕ) (g : StableGeneralLinear.GL F n) :
    ((rightProjectiveToModuleExact F).toFunctor.mapIso
      (FiniteProjectiveModule.StableFree.powerEndEquiv F n g).iso).hom ≫
        (powerModuleCoordinatesIso F n).hom =
      (powerModuleCoordinatesIso F n).hom ≫ (FGModuleCat.matrixToAut F n g).hom := by
  let e := (Core.inclusion (FiniteProjectiveModule.Category Fᵐᵒᵖ)).mapIso
    (FiniteProjectiveModule.rankOnePowerIsoFree Fᵐᵒᵖ n)
  let H := (rightProjectiveToModuleExact F).toFunctor
  change H.map (e.hom ≫ (RightMatrix.leftFreeAutEquiv F n g).hom ≫ e.inv) ≫
      (H.map e.hom ≫ (freeModuleCoordinatesIso F n).hom) =
    (H.map e.hom ≫ (freeModuleCoordinatesIso F n).hom) ≫ (FGModuleCat.matrixToAut F n g).hom
  have he : H.map e.inv ≫ H.map e.hom = 𝟙 _ := by
    rw [← H.map_comp, e.inv_hom_id, H.map_id]
  simp only [H.map_comp, Category.assoc]
  rw [← Category.assoc (H.map e.inv) (H.map e.hom) (freeModuleCoordinatesIso F n).hom,
    he, Category.id_comp]
  exact congrArg (fun k => H.map e.hom ≫ k) (freeModuleCoordinates_square F n g)

/-- The actual power action is conjugate to the standard matrix automorphism. -/
theorem powerModuleCoordinates_conjugate (n : ℕ) (g : StableGeneralLinear.GL F n) :
    Aut.autMulEquivOfIso (powerModuleCoordinatesIso F n)
      ((rightProjectiveToModuleExact F).toFunctor.mapIso
        (FiniteProjectiveModule.StableFree.powerEndEquiv F n g).iso) =
      FGModuleCat.matrixToAut F n g := by
  apply Iso.ext
  change (powerModuleCoordinatesIso F n).inv ≫
    (((rightProjectiveToModuleExact F).toFunctor.mapIso
      (FiniteProjectiveModule.StableFree.powerEndEquiv F n g).iso).hom ≫
        (powerModuleCoordinatesIso F n).hom) = _
  rw [powerModuleCoordinates_square]
  simp

/-- The same coordinate isomorphism in the client’s actual upper-universe SmallModel. -/
def upperPowerModuleCoordinatesIso (n : ℕ) :
    (equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
      ((rightProjectiveToModuleExact F).toFunctor.obj
        (FiniteProjectiveModule.rankOnePower Fᵐᵒᵖ n).of) ≅
      (equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
        (FGModuleCat.of F (Fin n → F)) :=
  (equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso (powerModuleCoordinatesIso F n)

/-- The chosen upper SmallModel functor retains the literal matrix conjugacy. -/
theorem upperPowerModuleCoordinates_conjugate (n : ℕ) (g : StableGeneralLinear.GL F n) :
    Aut.autMulEquivOfIso (upperPowerModuleCoordinatesIso F n)
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
        ((rightProjectiveToModuleExact F).toFunctor.mapIso
          (FiniteProjectiveModule.StableFree.powerEndEquiv F n g).iso)) =
      (equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
        (FGModuleCat.matrixToAut F n g) := by
  let H := (equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor
  have h := congrArg (fun a => H.mapIso a) (powerModuleCoordinates_conjugate F n g)
  apply Iso.ext
  simpa only [upperPowerModuleCoordinatesIso, Aut.autMulEquivOfIso,
    Functor.mapIso_hom, Functor.mapIso_inv,
    MulEquiv.coe_mk, Equiv.coe_fn_mk, Functor.map_comp] using congrArg Iso.hom h


/-- The actual transposed cubes of the power action and the standard matrix have the same class. -/
theorem upperPowerMatrixCube_class (n : ℕ) (g : StableGeneralLinear.GL F n) :
    (Quotient.mk' (Automorphism.Cube.automorphismFirstCube
      (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
        ((rightProjectiveToModuleExact F).toFunctor.obj
          (FiniteProjectiveModule.rankOnePower Fᵐᵒᵖ n).of))
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
        ((rightProjectiveToModuleExact F).toFunctor.mapIso
          (FiniteProjectiveModule.StableFree.powerEndEquiv F n g).iso))) :
      (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1) =
    Quotient.mk' (Automorphism.Cube.automorphismFirstCube
      (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
        (FGModuleCat.of F (Fin n → F)))
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
        (FGModuleCat.matrixToAut F n g))) := by
  rw [← upperPowerModuleCoordinates_conjugate F n g]
  exact (Automorphism.Isomorphism.automorphismFirstCube_class_conjugate _
    (upperPowerModuleCoordinatesIso F n) _).symm

end Quillen.Field
