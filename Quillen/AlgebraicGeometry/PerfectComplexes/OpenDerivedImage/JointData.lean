/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.JointComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Approximation

/-! # Genuine coherent opposite joint data on original weak restriction arrows -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- The actual component cocylinders and their proved cross-category comparison
give original fine opposite weak-arrow joint data. -/
def weakArrowJointData : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (weakArrowOpposite j)) :=
  WeakArrow.dualJointData (perfectWaldhausen X) (complexWaldhausen j)
    (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j) (complexCorestrict j)
    (complexCorestrict_exact j) (complexCorestrict_op_exact j) (complexOpposite_compatible j)
    (perfectOppositeJointData X) (complexOppositeJointData j) (complexCorestrictOpJointIso j)
    (complexCorestrictOpJointIso_inv_inl j) (complexCorestrictOpJointIso_inv_inr j)
    (complexCorestrictOpJointIso_inv_projection j)

end Quillen.PerfectComplexes.OpenDerivedImage
