/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionWaldhausen
public import Quillen.Waldhausen.Fibration.ExactChangeWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenComparison

/-!
# Original relative-open Waldhausen structure on affine sections

The original section category keeps its cofibrations and chosen zero. Weak equivalences
are detected by actual original evaluation into the existing bounded-flat relative-open
model. The original functor is retained by enlarging only its target weak class.
This construction makes no assertion about the full open K₀ endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- Original evaluation is exact into the original geometric relative-open structure. -/
theorem boundedFlatAffineSectionOpenEvaluation_exact :
    IsExact (boundedFlatAffineSectionWaldhausen R).cof
      (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatPerfectOpenWaldhausen j).cof (boundedFlatPerfectOpenWaldhausen j).weq
      (boundedFlatAffineOriginalEvaluation R) :=
  (boundedFlatAffineOriginalEvaluation_exact R).changeWeakTarget
    (boundedFlatPerfectOpenNested j)

/-- Actual relative-open weakness, retaining the original section cofibrations and zero. -/
def boundedFlatAffineSectionOpenWaldhausen : Structure (BoundedFlatAffineSections R) :=
  Structure.withInverseImageWeak (boundedFlatAffineSectionOpenEvaluation_exact j)

/-- The unchanged fine section weak class lies in the actual relative-open weak class. -/
def boundedFlatAffineSectionOpenNested :
    NestedWeakEquivalences (boundedFlatAffineSectionWaldhausen R) :=
  Structure.inverseImageWeakNested (boundedFlatAffineSectionOpenEvaluation_exact j)

/-- Evaluation preserves the new genuine coarse weak class by its defining original map. -/
theorem boundedFlatAffineSectionOpenEvaluation_coarse_exact :
    IsExact (boundedFlatAffineSectionOpenWaldhausen j).cof
      (boundedFlatAffineSectionOpenWaldhausen j).weq
      (boundedFlatPerfectOpenWaldhausen j).cof (boundedFlatPerfectOpenWaldhausen j).weq
      (boundedFlatAffineOriginalEvaluation R) :=
  Structure.withInverseImageWeak_exact (boundedFlatAffineSectionOpenEvaluation_exact j)

end Quillen.PerfectComplexes
