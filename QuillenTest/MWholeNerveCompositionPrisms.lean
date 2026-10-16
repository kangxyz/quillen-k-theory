/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionPrismEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionPrismNative

/-! Both exact composition prisms, complete endpoint references and whole varying side families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen Quillen.PerfectComplexes Quillen.PerfectComplexes.BassMWholeNerve
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open Quillen.PerfectComplexes.ProjectionRectangleParameters
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveCompositionPrisms
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Compact evaluation recovers the entire original laurent finite-product family. -/
theorem actual_laurent_prism_compact_native (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, s, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (BassH0Diagram.parameter (s, t), x)) :=
  laurent_prism_compact_native P u v w n q s t x

/-- The entire varying bottom side retains its exact original named H0 path. -/
theorem actual_laurent_prism_bottom_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, 0, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (((D BassH0Diagram.plusFace).symm.trans (D BassH0Diagram.minusFace)) t, x)) :=
  laurent_prism_bottom_side P u v w n q t x

/-- The entire varying top side retains its exact original named H0 path. -/
theorem actual_laurent_prism_top_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, 1, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (((Ppath BassH0Diagram.plusFace).trans
            (((K BassH0Diagram.plusFace).symm.trans (K BassH0Diagram.minusFace)).trans
              (Ppath BassH0Diagram.minusFace).symm)) t, x)) :=
  laurent_prism_top_side P u v w n q t x

/-- The entire varying plus side retains its exact original named H0 path. -/
theorem actual_laurent_prism_plus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, s, 0], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (L BassH0Diagram.plusFace s, x)) :=
  laurent_prism_plus_side P u v w n q s x

/-- The entire varying minus side retains its exact original named H0 path. -/
theorem actual_laurent_prism_minus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, s, 1], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (L BassH0Diagram.minusFace s, x)) :=
  laurent_prism_minus_side P u v w n q s x

/-- Compact evaluation recovers the entire original coefficient finite-product family. -/
theorem actual_coefficient_prism_compact_native (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, s, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (BassH0Diagram.parameter (s, t),
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) :=
  coefficient_prism_compact_native P u v w n q s t x

/-- The entire varying bottom side retains its exact original named H0 path. -/
theorem actual_coefficient_prism_bottom_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, 0, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (((D BassH0Diagram.plusFace).symm.trans (D BassH0Diagram.minusFace)) t,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) :=
  coefficient_prism_bottom_side P u v w n q t x

/-- The entire varying top side retains its exact original named H0 path. -/
theorem actual_coefficient_prism_top_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, 1, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (((Ppath BassH0Diagram.plusFace).trans
            (((K BassH0Diagram.plusFace).symm.trans (K BassH0Diagram.minusFace)).trans
              (Ppath BassH0Diagram.minusFace).symm)) t,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) :=
  coefficient_prism_top_side P u v w n q t x

/-- The entire varying plus side retains its exact original named H0 path. -/
theorem actual_coefficient_prism_plus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, s, 0], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (L BassH0Diagram.plusFace s,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) :=
  coefficient_prism_plus_side P u v w n q s x

/-- The entire varying minus side retains its exact original named H0 path. -/
theorem actual_coefficient_prism_minus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, s, 1], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (L BassH0Diagram.minusFace s,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) :=
  coefficient_prism_minus_side P u v w n q s x

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_laurent_prism_source_nodes (i : Fin 31) :
    laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2 (i, 0)) =
      ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassMWhole.nodes P u (v ≫ w)) (firstIndex i) :=
  laurent_prism_source_nodes P u v w i

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_coefficient_prism_source_nodes (i : Fin 31) :
    coefficientPrismNodes P u v w (Quillen.SimplexGrid.index 2 30 (0, i)) =
      ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassMWhole.nodes P (u ≫ v) w) (middleIndex i) :=
  coefficient_prism_source_nodes P u v w i

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_laurent_prism_target_nodes (i : Fin 31) :
    laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2 (i, 2)) =
      postcompNodes P u v w (firstIndex i) :=
  laurent_prism_target_nodes P u v w i

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_coefficient_prism_target_nodes (i : Fin 31) :
    coefficientPrismNodes P u v w (Quillen.SimplexGrid.index 2 30 (2, i)) =
      precompNodes P u v w (middleIndex i) :=
  coefficient_prism_target_nodes P u v w i

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_laurent_prism_source_face (s t : unitInterval) :
    laurentPrism P u v w ![0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, lower s, t] :=
  laurent_prism_source_face P u v w s t

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_laurent_prism_target_face (s t : unitInterval) :
    laurentPrism P u v w ![1, s, t] = postcompLift P u v w ![1, lower s, t] :=
  laurent_prism_target_face P u v w s t

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_coefficient_prism_source_face (s t : unitInterval) :
    coefficientPrism P u v w ![0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, upper (lower t)] :=
  coefficient_prism_source_face P u v w s t

/-- The exact original whole endpoint is retained, including every dependent reference. -/
theorem actual_coefficient_prism_target_face (s t : unitInterval) :
    coefficientPrism P u v w ![1, s, t] =
      precompLift P u v w ![1, upper s, upper (lower t)] :=
  coefficient_prism_target_face P u v w s t

/-- The original structure coordinate is independent of all three prism coordinates. -/
theorem laurent_independent_structure (n : ℕ) (q s t h : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) (n + 1)
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x h) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).structureMap n
          (CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
            (![q, s, t], x)) h :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ (laurentPrism P u v w) n
    ![q, s, t] x h

/-- Level zero keeps the whole prism and the actual original based point. -/
theorem laurent_level_zero_point (q s t : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) 0
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).point 0 :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ (laurentPrism P u v w) 0 ![q, s, t]

/-- The original structure coordinate is independent of all three prism coordinates. -/
theorem coefficient_independent_structure (n : ℕ) (q s t h : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) (n + 1)
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x h) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).structureMap n
          (CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
            (![q, s, t], x)) h :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ (coefficientPrism P u v w) n
    ![q, s, t] x h

/-- Level zero keeps the whole prism and the actual original based point. -/
theorem coefficient_level_zero_point (q s t : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) 0
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).point 0 :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ (coefficientPrism P u v w) 0 ![q, s, t]

/-- Every original level-zero input retains the literal two-half Laurent composition. -/
theorem laurent_whole_level_zero (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) 0
      (![q, s, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level 0
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) 0
          (BassH0Diagram.parameter (s, t), x)) :=
  laurent_prism_compact_native P u v w 0 q s t x

/-- Every original level-zero input retains the literal two-half coefficient composition. -/
theorem coefficient_whole_level_zero (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) 0
      (![q, s, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) 0
        (BassH0Diagram.parameter (s, t),
          (boundedFlatCoefficientCompositionHomotopy P u v).level 0 (q, x)) :=
  coefficient_prism_compact_native P u v w 0 q s t x

/-- Level zero retains the input loop's own independent coordinate. -/
theorem laurent_independent_input_loop (q s t h : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) 0
        (![q, s, t], γ)) h =
      CommonReferenceNerve.compactStageFamily _ 0 (laurentPrism P u v w)
        (![q, s, t], γ h) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ (laurentPrism P u v w)
    ![q, s, t] γ h

/-- Level zero retains the input loop's own independent coordinate. -/
theorem coefficient_independent_input_loop (q s t h : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) 0
        (![q, s, t], γ)) h =
      CommonReferenceNerve.compactStageFamily _ 0 (coefficientPrism P u v w)
        (![q, s, t], γ h) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply _ (coefficientPrism P u v w)
    ![q, s, t] γ h

end QuillenTest.MWholeNerveCompositionPrisms
