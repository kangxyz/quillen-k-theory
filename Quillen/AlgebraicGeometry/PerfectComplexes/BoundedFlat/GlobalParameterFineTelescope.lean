/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientTelescope

/-! # Actual stable comparison with the original fine ambient Bass telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex

/-- Spec comparison followed by the original global-to-coefficient telescope restriction. -/
def fineTelescopeComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterTelescope Q.left ⟶ boundedFlatCoefficientAmbientBassTelescopeFunctor Q :=
  (telescopeIso Q).hom ≫ telescopeRestriction Q

/-- The actual fine comparison is stable at every coefficient object. -/
theorem fineTelescopeComparison_stable
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fineTelescopeComparison Q).app a) :=
  (telescopeIso_stable Q a).comp (telescopeRestriction_isStableEquivalence Q a)

end Quillen.PerfectComplexes.GlobalParameterCoefficient
