/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGrading
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Cylinder
public import Quillen.Waldhausen.Fibration.Rows.EquivalenceJoint
public import Quillen.Waldhausen.Cofinality.GeneralGraded

/-!
# Actual full-open section joint cylinders and positive graded K-groups

The inverse of the original full-open evaluation equivalence transports the genuine
bounded-flat joint-cylinder data. Both directions are exact for the original structures.
The resulting data prove positive-degree vanishing for the unchanged quotient grading,
without a second-endpoint-section premise or any assumption on coefficient flatness.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual inverse evaluation equivalence is exact for the inherited section structure. -/
theorem boundedFlatAffineFullOpenSectionEquivalence_inverse_exact (a : Under R) :
    IsExact (boundedFlatPerfectWaldhausen (openSpace j a)).cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatAffineFullOpenSectionEquivalence j a).inverse :=
  Structure.ofEquivalence_inverse_exact (boundedFlatPerfectWaldhausen (openSpace j a))
    (boundedFlatAffineFullOpenSectionEquivalence j a)
    (boundedFlatAffineFullOpenSectionZero j a)
    (isZero_boundedFlatAffineSectionFullOpenImageZero j a)

/-- Original bounded-flat joint cylinders give actual joint data on the same section category. -/
def boundedFlatAffineFullOpenSectionJointData (a : Under R) :
    Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl
        (boundedFlatAffineFullOpenSectionWaldhausen j a)) :=
  Fibration.RowFactorization.JointData.ofExactEquivalence
    (boundedFlatPerfectWaldhausen (openSpace j a))
    (boundedFlatAffineFullOpenSectionWaldhausen j a)
    (boundedFlatAffineFullOpenSectionEquivalence j a).symm
    (boundedFlatAffineFullOpenSectionEquivalence_inverse_exact j a)
    (boundedFlatAffineFullOpenOriginalEvaluation_exact j a)
    (boundedFlatPerfectJointData (openSpace j a))

/-- The original positive K-groups of the actual quotient-graded section structure vanish. -/
theorem boundedFlatAffineFullOpenGradedSection_K_succ_subsingleton
    (a : Under R) (n : ℕ) :
    Subsingleton ((boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) :=
  (boundedFlatAffineFullOpenSectionGrading j a).coarse_K_succ_subsingleton_general
    (boundedFlatAffineFullOpenSectionJointData j a) n

end Quillen.PerfectComplexes
