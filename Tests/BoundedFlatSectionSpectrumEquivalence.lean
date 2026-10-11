/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumEquivalence

/-!
# Consumers of the actual original evaluation spectrum equivalence

All levels retain the unchanged comparison map. The whole inverse homotopy retains separate
comparison time and structure-map loop time, including the original degree-zero level.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u
namespace Quillen.Tests.BoundedFlatSectionSpectrumEquivalence

/-- Every level, including zero, is a complete weak equivalence of the original map. -/
theorem original_every_level (R : CommRingCat.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map n) :=
  boundedFlatAffineSectionEvaluation_level_isWeakHomotopyEquivalence R n

/-- The exact same original map is a stable equivalence. -/
theorem original_stable_map (R : CommRingCat.{u}) :
    LoopPrespectrum.IsStableEquivalence (boundedFlatAffineSectionEvaluationPrespectrumMap R) :=
  boundedFlatAffineSectionEvaluation_isStableEquivalence R

/-- The left inverse track starts at the two original continuous maps, even in degree zero. -/
theorem original_degree_zero_composite (R : CommRingCat.{u})
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (boundedFlatAffineSectionEvaluationLeftHomotopy R).level 0 (0, x) =
      (boundedFlatAffineSectionEvaluationInversePrespectrumMap R).map 0
        ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map 0 x) :=
  (boundedFlatAffineSectionEvaluationLeftHomotopy R).at_zero 0 x

/-- The same actual inverse track ends at the original point in every degree. -/
theorem original_inverse_endpoint (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionEvaluationLeftHomotopy R).level n (1, x) = x :=
  (boundedFlatAffineSectionEvaluationLeftHomotopy R).at_one n x

/-- Comparison time and structure loop time remain independent in the whole inverse track. -/
theorem independent_structure_time (R : CommRingCat.{u}) (n : ℕ) (r t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionEvaluationLeftHomotopy R).level (n+1)
        (r, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n
        ((boundedFlatAffineSectionEvaluationLeftHomotopy R).level n (r, x)) t :=
  (boundedFlatAffineSectionEvaluationLeftHomotopy R).comm n r x t

end Quillen.Tests.BoundedFlatSectionSpectrumEquivalence
