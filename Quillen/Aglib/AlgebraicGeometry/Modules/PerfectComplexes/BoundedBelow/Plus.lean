/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic

/-!
# The original lower-bounded perfect complex in the plus category

Only the perfectness proof is forgotten; the same actual complex and chain maps are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
/-- Forget only perfection, retaining the same original lower-bounded complex. -/
def boundedToPlus (X : Scheme.{u}) : BoundedBelow.Obj X ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (BoundedBelow.objects X).ι (fun K => K.property.2)


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
end
end
