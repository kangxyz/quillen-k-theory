/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.FlatPullback

/-!
# The two original lower-bounded pullback declarations agree

Both existing functors retain the literal original termwise flat pullback.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
/-- These two actual model wrappers have the same original flat pullback and chain maps. -/
lemma boundedFlatPullback_eq_native {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    SelfBaseChange.boundedFlatPullback f = FlasqueTwoSummands.boundedPullback f := rfl


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
end
end
