/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenRestrictionSquare

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionFullOpenRestriction


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenRestrictionNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenStructure

/-!
# Original coarse-section evaluation followed by full-open restriction

The functor is the unchanged original identity evaluation followed by the specified open
pullback. It is exact for the genuine relative-open source structure. Coefficient, zero and
scalar comparisons are supplied by the separate downstream owners.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- Actual evaluation and actual open restriction preserve the genuine Waldhausen classes. -/
theorem boundedFlatAffineSectionFullOpenRestriction_exact (a : Under R) :
    Waldhausen.IsExact (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).cof
      (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).weq
      (boundedFlatPerfectWaldhausen (openSpace j a)).cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineSectionFullOpenRestriction j a) :=
  (boundedFlatAffineSectionOpenEvaluation_coarse_exact (inclusion j a)).comp
    (boundedFlatAffineFullOpenRestriction_exact j a)


end Quillen.PerfectComplexes
