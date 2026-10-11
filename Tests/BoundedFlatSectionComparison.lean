/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionComparison

/-!
# Consumers of the unchanged original bounded-flat comparison

The comparison retains actual evaluation, both all-class inverse identities and the actual
original-prespectrum map inducing that same original K-equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.BoundedFlatSectionComparison

/-- Only actual evaluation and the original universe lift occur in the model map. -/
theorem actual_forward_functor (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionEvaluationModelMap R).functor =
      boundedFlatAffineOriginalEvaluation R ⋙ AsSmall.up :=
  boundedFlatAffineSectionEvaluationModelMap_functor R

/-- Every original bounded-flat K-class is recovered by the genuine inverse equivalence. -/
theorem every_original_class_recovered (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedFlatPerfectWaldhausen (Spec R)).K n) :
    boundedFlatAffineSectionKEquiv R n ((boundedFlatAffineSectionKEquiv R n).symm a) = a :=
  (boundedFlatAffineSectionKEquiv R n).apply_symm_apply a

/-- Every section K-class is recovered by the same actual equivalence. -/
theorem every_section_class_recovered (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedFlatAffineSectionWaldhausen R).K n) :
    (boundedFlatAffineSectionKEquiv R n).symm (boundedFlatAffineSectionKEquiv R n a) = a :=
  (boundedFlatAffineSectionKEquiv R n).symm_apply_apply a

/-- The actual original-prespectrum comparison induces that same original all-degree K-map. -/
theorem original_spectral_kmap (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedFlatAffineSectionWaldhausen R).K n) :
    originalZeroSpaceEquiv (boundedFlatPerfectWaldhausen (Spec R)) n
        (boundedFlatAffineSectionKEquiv R n a) =
      homotopyGroupMap ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map 0)
        ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map_point 0)
        (boundedFlatAffineSectionZeroSpaceEquiv R n a) :=
  boundedFlatAffineSectionEvaluationPrespectrumMap_zeroSpace R n a

/-- The map lands at the original geometric prespectrum's actual chosen basepoint. -/
theorem original_spectral_basepoint (R : CommRingCat.{u}) (n : ℕ) :
    (boundedFlatAffineSectionEvaluationPrespectrumMap R).map n
        ((boundedFlatAffineSectionPrespectrumFunctor.obj R).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).point n :=
  (boundedFlatAffineSectionEvaluationPrespectrumMap R).map_point n

end Quillen.Tests.BoundedFlatSectionComparison
