/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.JointComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Approximation

/-!
# Actual supported weak-arrow joint data

The original component supported cocylinders and their proved cross-category
natural isomorphism, including all three endpoint/projection equations,
construct genuine fine opposite weak-arrow JointData. No K-equivalence
conclusion is assumed.
-/
@[expose] public section

open Quillen.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) [Fact
  (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

/-- The actual component cocylinders and their proved cross-category comparison
give original fine opposite weak-arrow joint data. -/
def weakArrowJointData : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (weakArrowOpposite j T)) :=
  WeakArrow.dualJointData (perfectSupportedWaldhausen T.ι) (complexWaldhausen j T)
    (perfectSupportedOppositeWaldhausen T.ι) (complexOppositeWaldhausen j T) (complexCorestrict j T)
    (complexCorestrict_exact j T) (complexCorestrict_op_exact j T) (complexOpposite_compatible j T)
    (perfectSupportedOppositeJointData T.ι) (complexOppositeJointData j T)
      (complexCorestrictOpJointIso j T)
    (complexCorestrictOpJointIso_inv_inl j T) (complexCorestrictOpJointIso_inv_inr j T)
    (complexCorestrictOpJointIso_inv_projection j T)

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end
