/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenRestrictionNaturality
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionEvaluation

/-!
# Original section evaluation followed by full-open restriction

The unchanged identity evaluation is followed by the specified original geometric open pullback.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The exact original coarse-section-to-full-open functor, before chosen-zero normalization. -/
def boundedFlatAffineSectionFullOpenRestriction (a : Under R) :
    BoundedFlatAffineSections a.right ⥤ BoundedFlatPerfect (openSpace j a) :=
  boundedFlatAffineOriginalEvaluation a.right ⋙ boundedFlatAffineFullOpenRestriction j a

end Quillen.PerfectComplexes

end

end
