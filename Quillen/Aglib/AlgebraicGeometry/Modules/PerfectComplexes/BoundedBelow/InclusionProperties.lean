/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic

/-!
# The original lower-bounded full inclusion

Additivity and the original binary biproduct/coproduct preservation retain the literal
chain inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
instance boundedInclusion_additive (X : Scheme.{u}) :
    (BoundedBelow.inclusion X).Additive where
  map_add := by intros; rfl

instance boundedInclusion_preservesBinaryBiproducts (X : Scheme.{u}) :
    PreservesBinaryBiproducts (BoundedBelow.inclusion X) := by
  let : PreservesFiniteBiproducts (BoundedBelow.inclusion X) := inferInstance
  exact preservesBinaryBiproducts_of_preservesBiproducts _

instance boundedInclusion_preservesBinaryCoproducts (X : Scheme.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (BoundedBelow.inclusion X) :=
  preservesBinaryCoproducts_of_preservesBinaryBiproducts _


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
end
end
