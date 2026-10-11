/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumNaturality

/-!
# Original coefficient comparison consumers

The whole evaluation track retains both actual coefficient composites and independent structure
time. Its zeroth level is the original based-loop map.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open scoped unitInterval
universe u
namespace Quillen.Tests.BoundedFlatSectionSpectrumNaturality

/-- The initial endpoint uses literal strict restriction followed by original evaluation. -/
theorem original_source {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level n (0, x) =
      (boundedFlatAffineSectionEvaluationPrespectrumMap S).map n
        ((boundedFlatAffineSectionPrespectrumFunctor.map f).map n x) :=
  (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).at_zero n x

/-- The terminal endpoint retains the original normalized geometric pullback. -/
theorem original_target {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level n (1, x) =
      (boundedFlatPerfectPrespectrumMap (Spec.map f)).map n
        ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map n x) :=
  (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).at_one n x

/-- The actual degree-zero loop has the original target endpoint. -/
theorem original_zero_level {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level 0 (1, x) =
      (boundedFlatPerfectPrespectrumMap (Spec.map f)).map 0
        ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map 0 x) :=
  original_target f 0 x

/-- The comparison parameter is independent of the original structure loop parameter. -/
theorem independent_structure_time {R S : CommRingCat.{u}} (f : R ⟶ S)
    (n : ℕ) (r t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level (n+1)
        (r, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t) =
      (Quillen.Waldhausen.IteratedS.originalPrespectrum
        (boundedFlatPerfectWaldhausen (Spec S))).structureMap n
        ((boundedFlatAffineSectionEvaluationCoefficientHomotopy f).level n (r, x)) t :=
  (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).comm n r x t

end Quillen.Tests.BoundedFlatSectionSpectrumNaturality
