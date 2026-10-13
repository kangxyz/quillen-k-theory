/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ProjectionFormula
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.AffineRetract
/-!
# Projection formula for affine vector-bundle coefficients

The original geometric unit proves the unit case. Actual finite-free retractions
then prove the projection formula for finite locally free coefficients on an
affine target, for an arbitrary scheme morphism and arbitrary source module.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
namespace Quillen.SchemeSheaf
variable {X Y : Scheme.{u}}
/-- The literal projection-formula arrow is invertible on the structure module. -/
instance isIso_projectionFormulaMap_unit (f : X ⟶ Y) (M : X.Modules) :
    IsIso (projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) M) := by
  let e := (moduleTensorRightFunctor X M).mapIso (pullbackUnitIso f) ≪≫
    (tensorLeftUnitIso X.sheaf).app M
  have : IsIso (projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) M ≫
      (Scheme.Modules.pushforward f).map e.hom) := by
    change IsIso (projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) M ≫
      (Scheme.Modules.pushforward f).map
        ((moduleTensorRightFunctor X M).map (pullbackUnitIso f).hom ≫
          (tensorLeftUnitIso X.sheaf).hom.app M))
    rw [projectionFormulaMap_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward f).map e.hom)
/-- For an affine target, an actual finite-free retract proves the original projection formula. -/
theorem isIso_projectionFormulaMap_affine (R : CommRingCat.{u}) (f : X ⟶ Spec R)
    (E : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) E] (M : X.Modules) :
    IsIso (projectionFormulaMap f E M) := by
  let : IsIso ((projectionFormulaNatTrans f M).app
      (SheafOfModules.unit (Spec R).ringCatSheaf)) := isIso_projectionFormulaMap_unit f M
  exact isIso_app_affineBundle_of_unit_general R
    (moduleTensorRightFunctor (Spec R) ((Scheme.Modules.pushforward f).obj M))
    (Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M ⋙ Scheme.Modules.pushforward f)
    (projectionFormulaNatTrans f M) E
end Quillen.SchemeSheaf
end
