/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic

/-!
# The original full flasque-to-perfect inclusion

Only the two original lower-bound and flasque proof wrappers are forgotten. The actual complex and all chain maps are retained.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.FlasqueBoundedBelow

/-- The literal original full inclusion into all locally perfect complexes. -/
def perfectInclusion (X : Scheme.{u}) : Obj X ⥤ Perfect X :=
  inclusion X ⋙ BoundedBelow.inclusion X

end Quillen.PerfectComplexes.FlasqueBoundedBelow

end

end
