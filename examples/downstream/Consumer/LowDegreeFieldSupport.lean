/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.FiniteSupport.Decomposition
public import Quillen.KTheory.Field.MatrixCubeComparison

/-!
# Upper-universe residue-family consumers

These clients use the actual evaluation and singleton K-maps in the universe
required for coherent small models. They retain explicit degrees rather than
assuming a decomposition in every degree as background data.
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Pi
open Quillen.FiniteSupport
open scoped DirectSum

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

universe u

namespace Consumer.LowDegreeFieldSupport

/-- The literal positive standard cube retains determinant after actual tensor extension. -/
theorem fieldMatrixTensorDet {F L : Type u} [Field F] [Field L] (f : F →+* L)
    (n : ℕ) (g : Quillen.StableGeneralLinear.GL F n) :
    Quillen.Field.moduleDetEquiv L
        ((Quillen.Field.finiteModuleExtensionExact f).smallKMap.{u + 1} 1
          (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube
            (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u + 1}
            ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.obj
              (FGModuleCat.of F (Fin n → F)))
            ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).functor.mapIso
              (FGModuleCat.matrixToAut F n g))))) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  exact (Quillen.Field.moduleDetEquiv_scalarExtension F f _).trans
    (congrArg (Units.map f.toMonoidHom) (Quillen.Field.moduleDetEquiv_matrix_cube F n g))

variable {I : Type u} (C : I → Type (u + 1))
  [∀ i, Category.{u + 1} (C i)] [∀ i, Abelian (C i)]

/-- The residue-family K1 theorem consumes the original evaluation maps. -/
theorem degreeOneCoordinates :
    Nonempty {e : Additive ((finiteCategoryExactStructure C).K 1) ≃+
      ⨁ i, Additive ((abelianExactStructure (C i)).K 1) //
      ∀ a i, e a i = ((finiteCategoryEvaluation C i).KMap 1).toAdditive a} :=
  ⟨K1DecompositionEquiv.{u, u + 1} C, fun _ _ => rfl⟩

/-- Every finite K2 residue family lifts through the sum of the original inclusions. -/
theorem degreeTwoFiniteLift
    (a : ⨁ i, Additive ((abelianExactStructure (C i)).K 2)) :
    ∃ b : Additive ((finiteCategoryExactStructure C).K 2),
      (∀ i, ((finiteCategoryEvaluation C i).KMap 2).toAdditive b = a i) ∧
      b = ∑ i ∈ a.support,
        ((singletonExactInclusion C i).KMap 2).toAdditive (a i) := by
  refine ⟨(K2DecompositionEquiv.{u, u + 1} C).symm a, ?_, decompositionKEquiv_symm_apply.{u, u + 1} C 1 a⟩
  intro i
  have h := congrArg (fun b => b i) ((K2DecompositionEquiv.{u, u + 1} C).apply_symm_apply a)
  exact h

end Consumer.LowDegreeFieldSupport
