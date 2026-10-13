/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Closure
public import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint
public import Quillen.Waldhausen.Fibration.Rows.ReflexiveFactorization

/-! # Original fine joint-cylinder data for strict-perfect complexes

The actual strict cone and shift provide the original fine joint functor,
its quasi-isomorphism projection, and the genuine second-endpoint section.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.StrictOpenWeakImage
open Waldhausen Fibration
/-- The original strict cone gives genuine fine joint data. -/
def fineJointData (X : Scheme.{u}) : RowFactorization.JointData (NestedWeakEquivalences.refl
  (strictWaldhausen X)) :=
  complexJointDataOfNested (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f)
    (fun _ hK ↦ strictPerfect_shift hK 1) (NestedWeakEquivalences.refl (strictWaldhausen X))

/-- The original second endpoint has its actual strict section equation. -/
theorem fineJointData_section (X : Scheme.{u}) :
    RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl (strictWaldhausen X))
      (fineJointData X) :=
  complexJointDataOfNested_secondEndpointSection (strictPerfect X)
    (fun hK hL f ↦ strictPerfect_mappingCone hK hL f)
    (fun _ hK ↦ strictPerfect_shift hK 1) (NestedWeakEquivalences.refl (strictWaldhausen X))

end Quillen.PerfectComplexes.StrictOpenWeakImage
