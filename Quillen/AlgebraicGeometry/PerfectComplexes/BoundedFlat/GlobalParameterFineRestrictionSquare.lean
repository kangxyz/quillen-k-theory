/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterFullRestrictionTelescopeSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterFineTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalFullOpenTelescopeSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeSquares

/-! # The literal original fine full-open telescope comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual comparison retains both original fine full-open quotient maps. -/
theorem fine_fullRestriction_square :
    Functor.whiskerLeft specUnder (parameterTelescopeRestriction f) ≫
        fineTelescopeComparison P =
      fineTelescopeComparison Q ≫ boundedFlatCoefficientAmbientBassTelescopeOpen f ≫
        boundedFlatCoefficientOpenBassTelescopeRestriction f := by
  dsimp only [fineTelescopeComparison]
  rw [← Category.assoc, fullRestriction_telescope_square]
  simp only [Category.assoc]
  rw [FullOpenTelescope.restriction_square, ← Category.assoc (LocalizationTelescope.openMap f),
    LocalizationTelescope.open_square]
  simp only [Category.assoc]

end Quillen.PerfectComplexes.GlobalParameterCoefficient
