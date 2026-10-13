/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentEvaluationHomotopy

/-!
# Original Laurent evaluation square consumers

Both unit actions and the original coefficient track remain literal on all four edges.
The zeroth-level loop coordinate and the independent prespectrum structure time are retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange
universe u
namespace QuillenTest.SectionLaurentEvaluationHomotopy

open Quillen
variable (R : CommRingCat.{u})

/-- The strict edge is the original section unit followed by original Laurent evaluation. -/
theorem original_strict_edge (n : ℕ) (s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level n (0, (s, x)) =
      (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))).map n
        ((boundedFlatAffineSectionLaurentUnitHomotopy R).level n (s, x)) :=
  (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).at_zero n s x

/-- The opposite edge is the unchanged raw normalized Laurent action after actual evaluation. -/
theorem original_raw_edge (n : ℕ) (s : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level n (1, (s, x)) =
      (boundedFlatLaurentUnitHomotopy R).level n
        (s, (boundedFlatAffineSectionEvaluationPrespectrumMap R).map n x) :=
  (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).at_one n s x

/-- The actual coefficient comparison is retained at the beginning of the unit interval. -/
theorem original_coefficient_left_edge (n : ℕ) (r : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level n (r, (0, x)) =
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)).level n (r, x) :=
  (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).left n r x

/-- The very same original coefficient comparison remains at the end of the unit interval. -/
theorem original_coefficient_right_edge (n : ℕ) (r : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level n (r, (1, x)) =
      (boundedFlatAffineSectionEvaluationCoefficientHomotopy
        (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)).level n (r, x) :=
  (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).right n r x

/-- The degree-zero source edge keeps the original loop parameter independently of unit time. -/
theorem original_zero_loop_edge (s t : unitInterval)
    (p : Path (stagePoint 0 (boundedFlatAffineSectionModel R))
      (stagePoint 0 (boundedFlatAffineSectionModel R))) :
    Path.toContinuousMap (show Path _ _ from
      (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level 0 (0, (s, p))) t =
      SSet.toTop.map ((stages 0).map
        (boundedFlatAffineSectionEvaluationModelMap (.of (LaurentPolynomial R))))
          (stageTransformationTopHomotopy 0
            (F := boundedFlatAffineSectionModelMap (laurentCoefficient R))
            (G := boundedFlatAffineSectionModelMap (laurentCoefficient R))
            (boundedFlatAffineSectionLaurentModelUnit R)
            (boundedFlatAffineSectionLaurentModelUnit_weak R) (s, p t)) := by
  exact congrArg
    (fun q : Path
      (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))))
      (stagePoint 0 (modelOf
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R)))))) => q t)
    (original_strict_edge R 0 s p)

/-- Neither whole homotopy coordinate is identified with the original structure time. -/
theorem original_independent_structure_time (n : ℕ) (r s t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level (n + 1)
      (r, (s, (boundedFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x t)) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))))).structureMap n
      ((boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level n (r, (s, x))) t :=
  (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).comm n r s x t

/-- Every relative-boundary point remains the literal input to the actual square collapse. -/
theorem original_relative_square_collapse (n : ℕ) (z : unitInterval × unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionLaurentEvaluationUnitSquare R).level n
      ((Quillen.ThreeSideSquare.collapse z).1, ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatAffineSectionLaurentEvaluationUnitBoundary R).level n (z.1, (z.2, x)) :=
  (boundedFlatAffineSectionLaurentEvaluationUnitBoundary R).toSquare_collapse n z x

end QuillenTest.SectionLaurentEvaluationHomotopy
