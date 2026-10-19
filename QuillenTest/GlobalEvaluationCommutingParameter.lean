/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputCommutingParameter

/-! Regression checks for the exact eight-node evaluation square and its independent clocks. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalEvaluationCommutingParameter
open GlobalBassEvaluation GlobalSectionChangeIndex

/-- The actual left boundary advances at its original affine time, without a pause. -/
theorem left_clock_weight (r : unitInterval) :
    (InputCommutingParameter.parameter (r, 0)).weights (3 : Fin 8) = (r : ℝ) := by
  rw [InputCommutingParameter.parameter_left]
  simp [edge, StdSimplex.weights_duple]

variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
  (h : p ≫ v = q ≫ w)

/-- The shared total vertex keeps the complete original dependent evaluation anchor. -/
theorem shared_total_anchor :
    InputCommutingSimplex.nodes p v q w h
        (InputCommutingSimplex.secondFace.toOrderHom 1) =
      ⟨InputCommutingSimplex.totalMap p v, evaluationComparisonIso (p ≫ v)⟩ :=
  (InputCommutingSimplex.second_nodes p v q w h 1).trans
    ((InputCommutingSimplex.secondNodes_one p v q w h).trans
      (InputCommutingSimplex.firstNodes_one p v))

/-- The whole continuous family is tested before taking any pointwise or boundary restriction. -/
noncomputable def scalarFamily (n : ℕ) :
    C(unitInterval × (unitInterval × (prespectrum (globalModel.obj (op C))).space n),
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :=
  (prespectrumSimplexFamily (InputCommutingSimplex.simplex p v q w h) n).comp
    ⟨fun z => (InputCommutingParameter.parameter (z.1, z.2.1), z.2.2), by fun_prop⟩

/-- Both scalar coordinates realize the entire specified native square at every level. -/
theorem whole_native_square (n : ℕ) :
    scalarFamily p v q w h n = (InputCommutingSquare.square p v q w h).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, s, x⟩
  exact InputCommutingParameter.native p v q w h n r s x

/-- The exact affine edge realizes the original first evaluation leg at its unchanged time. -/
theorem original_left_track (n : ℕ) (r : unitInterval)
    (x : (prespectrum (globalModel.obj (op C))).space n) :
    prespectrumSimplexFamily (InputCommutingSimplex.simplex p v q w h) n
        (edge (k := 7) 0 3 r, x) = (InputCommutingSquare.firstLeg p v).level n (r, x) := by
  rw [← InputCommutingParameter.parameter_left]
  exact (InputCommutingParameter.native p v q w h n r 0 x).trans
    ((InputCommutingSquare.square p v q w h).left n r x)

/-- Genuine level zero retains a third independent input-loop coordinate. -/
theorem native_zero_loop (r s t : unitInterval)
    (x : Path (stagePoint 0 (globalModel.obj (op C)))
      (stagePoint 0 (globalModel.obj (op C)))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen A)))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen A))) from
      (InputCommutingSquare.square p v q w h).level 0 (r, (s, x))) t =
        stageSimplexBarycentric (InputCommutingSimplex.simplex p v q w h) 0
          (InputCommutingParameter.parameter (r, s), x t) :=
  (congrArg (fun y : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen A)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen A))) => y t)
    (InputCommutingParameter.native p v q w h 0 r s x).symm).trans
      (prespectrumSimplexFamily_zero_apply (InputCommutingSimplex.simplex p v q w h)
        (InputCommutingParameter.parameter (r, s)) x t)

end QuillenTest.GlobalEvaluationCommutingParameter
