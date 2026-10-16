/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Additivity of the original D-plus quotient

The existing declaration namespaces retain additivity of the actual plus quotient functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
local instance derivedPlusQ_additive (X : Scheme.{u}) :
    (DerivedCategory.Plus.Q (C := X.Modules)).Additive := by
  dsimp [DerivedCategory.Plus.Q]
  infer_instance


end Quillen.PerfectComplexes.ProjectiveLine.Euler
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
local instance derivedPlusQ_additive (Y : Scheme.{u}) :
    (DerivedCategory.Plus.Q (C := Y.Modules)).Additive := by
  dsimp [DerivedCategory.Plus.Q]
  infer_instance


end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEuler
end
end
