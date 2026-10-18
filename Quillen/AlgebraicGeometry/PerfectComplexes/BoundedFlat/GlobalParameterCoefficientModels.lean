/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenPairDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentAction
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseCanonicalRow

/-! # The original integral Spec row comparison lifted through the strict global Model -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The actual symmetry and terminal-map transport give an isomorphism of original Model rows. -/
def parameterRowModelIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ ParameterModels.ambient Q.left ≅ globalRow Q :=
  (Functor.associator specUnder (baseProductFunctor (toIntegerBase Q.left)).op globalModel).symm ≪≫
    Functor.isoWhiskerRight (canonicalParameterRowIso Q) globalModel ≪≫
      Functor.associator (row Q) (functor (CommRingCat.of (ULift.{u} ℤ))) globalModel

/-- Its component is exactly the original global pullback along the complete geometric iso. -/
theorem parameterRowModelIso_hom_app (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterRowModelIso Q).hom.app a = globalModel.map (canonicalRowIso Q a).hom.op := by
  change 𝟙 _ ≫ globalModel.map (canonicalRowIso Q a).hom.op ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- Compose actual row symmetry with the unchanged original coefficient restriction. -/
def parameterCoefficientRestriction (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ ParameterModels.ambient Q.left ⟶ boundedFlatCoefficientSectionModelRow Q :=
  (parameterRowModelIso Q).hom ≫ rowRestriction Q

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
