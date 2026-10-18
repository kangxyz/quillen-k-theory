/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalFullOpenModels

/-! # The actual full-open restriction square of integral parameter Models -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original full restriction, retaining its actual change-of-weakness factorization. -/
def parameterFullRestriction : ParameterModels.ambient Q.left ⟶ ParameterModels.ambient P.left :=
  ParameterModels.changeWeak f.left ≫ ParameterModels.openRestriction f.left

/-- Actual row symmetry commutes with the complete original full-open restriction. -/
theorem fullRestriction_model_square :
    Functor.whiskerLeft specUnder (parameterFullRestriction f) ≫ (parameterRowModelIso P).hom =
      (parameterRowModelIso Q).hom ≫ globalOpenFineRestriction f := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, parameterRowModelIso_hom_app]
  change globalModel.map
      ((baseProductTransformation (toIntegerBase P.left) (toIntegerBase Q.left)
        f.left (toIntegerBase_naturality f.left)).app (Spec a.right)).op ≫
      globalModel.map (canonicalRowIso P a).hom.op =
    globalModel.map (canonicalRowIso Q a).hom.op ≫ globalModel.map (schemeMap f a).op
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← op_comp, ← op_comp, ← canonicalRowIso_scheme]

end Quillen.PerfectComplexes.GlobalParameterCoefficient
