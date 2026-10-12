/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionEvaluation

/-!
# Exactness of original full-open section restriction

The proved original evaluation equality transports the existing relative-open exactness.
Actual full and faithful target evaluation reflects zero objects and pushouts, while the
inherited Waldhausen classes are detected by this same evaluation. The original section
restriction therefore preserves all four exactness requirements.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation

/-- Evaluation of the original section restriction retains the genuine original exact functor. -/
theorem boundedFlatAffineFullOpenSectionRestriction_evaluation_exact (a : Under R) :
    Waldhausen.IsExact (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).cof
      (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).weq
      (boundedFlatPerfectWaldhausen (openSpace j a)).cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineFullOpenSectionRestriction j a ⋙
        boundedFlatAffineFullOpenOriginalEvaluation j a) := by
  rw [boundedFlatAffineFullOpenSectionRestriction_comp_evaluation]
  exact boundedFlatAffineSectionFullOpenRestriction_exact j a

/-- The original section restriction preserves zero objects, cofibrations, weak maps
and pushouts. -/
theorem boundedFlatAffineFullOpenSectionRestriction_exact (a : Under R) :
    Waldhausen.IsExact (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).cof
      (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).weq
      (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatAffineFullOpenSectionRestriction j a) where
  zero hx := IsZero.of_full_of_faithful_of_isZero
    (boundedFlatAffineFullOpenOriginalEvaluation j a) _
    ((boundedFlatAffineFullOpenSectionRestriction_evaluation_exact j a).zero hx)
  cofibration f hf :=
    (boundedFlatAffineFullOpenSectionRestriction_evaluation_exact j a).cofibration f hf
  weak f hf := (boundedFlatAffineFullOpenSectionRestriction_evaluation_exact j a).weak f hf
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedFlatAffineFullOpenOriginalEvaluation j a)
    exact (boundedFlatAffineFullOpenSectionRestriction_evaluation_exact j a).pushout hi hp

end Quillen.PerfectComplexes
