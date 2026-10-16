/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Basic

/-!
# Original joint section evaluation into perfect complexes

The literal identity evaluation is followed by the unchanged bounded-flat inclusion.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- Native open identity evaluation followed by the original bounded-flat perfect inclusion. -/
def boundedFlatCoefficientFullOpenPerfectEvaluation (_f : P ⟶ Q) (a : Under R) :
    BoundedFlatCoefficientSections (op P, a) ⥤ Perfect (space (op P, a)) :=
  boundedFlatCoefficientOriginalEvaluation (op P, a) ⋙
    boundedFlatPerfectInclusion (space (op P, a))

end Quillen.PerfectComplexes

end

end
