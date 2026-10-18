/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Algebra.Group.StableFieldDeterminant
import Quillen.KTheory.Field.MatrixCubeComparison
import Quillen.KTheory.FiniteSupport.Decomposition
import Mathlib.Algebra.Field.ZMod

/-! Small-field and sparse-family regression properties on the original maps. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Pi
open Quillen.StableGeneralLinear Quillen.FiniteSupport
open scoped DirectSum

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

namespace QuillenTest.LowDegreeFieldSupport

/-- Rank zero is a genuine determinant-one representative. -/
theorem rankZero (F : Type*) [Field F] (g : Quillen.StableGeneralLinear.GL F 0) :
    quotientDetEquiv F (quotientMap F (of F 0 g)) = 1 := by
  rw [quotientDetEquiv_of]
  apply Units.ext
  exact Matrix.det_fin_zero

/-- The stable quotient over the three-element field retains its nontrivial unit. -/
theorem threeElementUnit_nontrivial : unitClass (ZMod 3) (-1) ≠ 1 := by
  intro h
  have h' : (-1 : (ZMod 3)ˣ) = 1 := by
    simpa using congrArg (quotientDet (ZMod 3)) h
  have h'' := congrArg (fun a : (ZMod 3)ˣ => (a : ZMod 3)) h'
  exact (by decide : (-1 : ZMod 3) ≠ 1) h''

universe u v

/-- The actual positive cube uses the same standard matrix and upper SmallModel as its consumer. -/
private def standardMatrixCube (F : Type u) [Field F] (n : ℕ)
    (g : Quillen.StableGeneralLinear.GL F n) :
    (ModuleCat.finiteModuleExactStructure.{u, u} F).SmallK.{u + 1} 1 :=
  Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube
    (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
    ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
      (FGModuleCat.of F (Fin n → F)))
    ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
      (FGModuleCat.matrixToAut F n g)))

/-- The literal rank-zero cube is trivial in the original upper finite-module K1. -/
theorem rankZeroCube (F : Type u) [Field F] (g : Quillen.StableGeneralLinear.GL F 0) :
    standardMatrixCube F 0 g = 1 := by
  apply (Quillen.Field.moduleDetEquiv F).injective
  rw [map_one]
  change Quillen.Field.moduleDetEquiv F
    (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube _ _ _)) = 1
  rw [Quillen.Field.moduleDetEquiv_matrix_cube]
  apply Units.ext
  exact Matrix.det_fin_zero

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Over F5 the positive rank-one cube has value 2, whose inverse is different. -/
theorem fiveElementCubeOrientation :
    Quillen.Field.moduleDetEquiv (ZMod 5)
        (standardMatrixCube (ZMod 5) 1
          (Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.mk0 (2 : ZMod 5) (by decide)))) =
      Units.mk0 (2 : ZMod 5) (by decide) ∧
      (Units.mk0 (2 : ZMod 5) (by decide))⁻¹ ≠ Units.mk0 (2 : ZMod 5) (by decide) := by
  constructor
  · change Quillen.Field.moduleDetEquiv (ZMod 5)
      (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube _ _ _)) = _
    rw [Quillen.Field.moduleDetEquiv_matrix_cube, Matrix.GeneralLinearGroup.det_scalar]
    simp
  · intro h
    have hmul := mul_inv_cancel (Units.mk0 (2 : ZMod 5) (by decide))
    rw [h] at hmul
    have hval := congrArg (fun a : (ZMod 5)ˣ => (a : ZMod 5)) hmul
    exact (by decide : (2 : ZMod 5) * 2 ≠ 1) hval

/-- Literal tensor extension preserves determinant on the transported matrix representative. -/
theorem tensorMatrixDet {F L : Type u} [Field F] [Field L] (f : F →+* L)
    (n : ℕ) (g : Quillen.StableGeneralLinear.GL F n) :
    Quillen.Field.moduleDetEquiv L
        ((Quillen.Field.finiteModuleExtensionExact f).smallKMap.{u + 1} 1
          (Quillen.Field.elementaryUpperModuleKOneEquiv F (quotientMap F (of F n g)))) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  rw [Quillen.Field.moduleDetEquiv_scalarExtension,
    Quillen.Field.elementaryUpperModuleKOneEquiv_quotientMap,
    Quillen.Field.moduleDetEquiv_matrix]

variable {I : Type u} (C : I → Type (max u v))
  [∀ i, Category.{max u v} (C i)] [∀ i, Abelian (C i)]

/-- Two original inclusion maps assemble the corresponding sparse coordinate family. -/
theorem twoCoordinateAssembly (n : ℕ) (i j : I)
    (a : (abelianExactStructure (C i)).K (n + 1))
    (b : (abelianExactStructure (C j)).K (n + 1)) :
    decompositionKEquiv C n
        (Additive.ofMul ((singletonExactInclusion C i).KMap (n + 1) a *
          (singletonExactInclusion C j).KMap (n + 1) b)) =
      DirectSum.of _ i (Additive.ofMul a) + DirectSum.of _ j (Additive.ofMul b) := by
  change decompositionKEquiv C n
    (Additive.ofMul ((singletonExactInclusion C i).KMap (n + 1) a) +
      Additive.ofMul ((singletonExactInclusion C j).KMap (n + 1) b)) = _
  rw [map_add, decompositionKEquiv_singleton, decompositionKEquiv_singleton]

/-- The empty family has trivial actual K2, without choosing coordinate zero objects. -/
theorem emptyFamilyKTwo (D : Empty → Type v)
    [∀ i, Category.{v} (D i)] [∀ i, Abelian (D i)]
    (a : Additive ((finiteCategoryExactStructure D).K 2)) : a = 0 := by
  apply (K2DecompositionEquiv D).injective
  ext i
  exact i.elim

end QuillenTest.LowDegreeFieldSupport
