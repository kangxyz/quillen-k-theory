/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficitGrading
public import Quillen.Waldhausen.Cofinality.ComplementMap

/-!
# The original image-quotient grading on full-open sections

The grading is pulled back along the actual identity evaluation followed by the original
bounded-flat inclusion. Its values lie in the unchanged raw-perfect image quotient. The
coarse structure keeps the same section category, cofibrations and inherited global zero.
No coefficient action, restriction comparison or inherited-seed compatibility is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Actual full-open identity evaluation followed by the original perfect inclusion. -/
def boundedFlatAffineFullOpenPerfectEvaluation (a : Under R) :
    BoundedFlatAffineFullOpenSections j a ⥤ Perfect (openSpace j a) :=
  boundedFlatAffineFullOpenOriginalEvaluation j a ⋙ boundedFlatPerfectInclusion (openSpace j a)

/-- Both original functors supply genuine exactness of the displayed composite. -/
theorem boundedFlatAffineFullOpenPerfectEvaluation_exact (a : Under R) :
    IsExact (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (perfectWaldhausen (openSpace j a)).cof (perfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineFullOpenPerfectEvaluation j a) :=
  (boundedFlatAffineFullOpenOriginalEvaluation_exact j a).comp
    (boundedFlatPerfectInclusion_exact (openSpace j a))

/-- The actual raw-perfect image quotient grades the original section objects by evaluation. -/
def boundedFlatAffineFullOpenSectionGrading (a : Under R) :
    Cofinality.Grading (boundedFlatAffineFullOpenSectionWaldhausen j a)
      (AlgebraicGrothendieck.ImageQuotient (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a)) (perfectOpenRestrict_waldhausenExact (inclusion j a))) :=
  (perfectOpenDeficitGrading (inclusion j a)).comap
    (boundedFlatAffineFullOpenPerfectEvaluation_exact j a)

/-- Every grade is exactly the original evaluated object's quotient class. -/
theorem boundedFlatAffineFullOpenSectionGrading_value (a : Under R)
    (S : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenSectionGrading j a).value S =
      (perfectOpenDeficitGrading (inclusion j a)).value
        ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj S) := rfl

/-- Only weakness changes: the original inherited section zero remains literal. -/
theorem boundedFlatAffineFullOpenSectionGrading_zero (a : Under R) :
    (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.zero =
      boundedFlatAffineFullOpenSectionZero j a := rfl

/-- Evaluation remains exact for the actual endpoint-grade weak classes. -/
theorem boundedFlatAffineFullOpenSectionGradingEvaluation_exact (a : Under R) :
    IsExact (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.cof
      (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.weq
      (perfectOpenDeficitGrading (inclusion j a)).coarseStructure.cof
      (perfectOpenDeficitGrading (inclusion j a)).coarseStructure.weq
      (boundedFlatAffineFullOpenPerfectEvaluation j a) where
  zero := (boundedFlatAffineFullOpenPerfectEvaluation_exact j a).zero
  cofibration := (boundedFlatAffineFullOpenPerfectEvaluation_exact j a).cofibration
  weak _ h := h
  pushout := (boundedFlatAffineFullOpenPerfectEvaluation_exact j a).pushout

/-- Original section objects and inherited zero, with the genuine pulled-back grade weakness. -/
def boundedFlatAffineFullOpenGradedSectionModel (a : Under R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatAffineFullOpenSections j a),
    (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure⟩

end Quillen.PerfectComplexes
