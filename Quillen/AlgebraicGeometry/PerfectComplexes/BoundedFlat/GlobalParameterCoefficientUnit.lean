/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseLaurentCoefficient
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterLaurentUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentAction

/-! # Original Laurent units under the actual integral parameter comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex ParameterLaurentUnit

/-- The actual complete Spec-row pullback preserves the same forward Laurent unit. -/
theorem ambientUnit_preserves
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Preserves (globalModel.map (laurentParameterIso Q a).hom.op).functor
      (ambientUnit Q.left (specUnder.obj a)) (globalLaurentUnit Q a) := by
  apply globalUnit_reindex_of_eq
  exact laurentParameterIso_unit Q a

end Quillen.PerfectComplexes.GlobalParameterCoefficient
