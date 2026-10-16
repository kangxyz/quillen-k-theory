/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Support

/-!
# Original supported joint evaluation into perfect complexes

Actual supported evaluation is followed by the literal support-preserving bounded-flat inclusion.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation

/-- Original supported native evaluation followed by the actual supported perfect inclusion. -/
def boundedFlatCoefficientSupportedFullOpenPerfectEvaluation (a : Under R) :
    BoundedFlatCoefficientSupportedOpenSections f T a ⥤
      (perfectSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).FullSubcategory :=
  boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientOpenSupportOpen f T a).ι ⋙
    boundedFlatPerfectSupportedInclusion (boundedFlatCoefficientOpenSupportOpen f T a).ι

end Quillen.PerfectComplexes

end

end
