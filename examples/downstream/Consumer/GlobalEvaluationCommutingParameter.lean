/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputCommutingParameter

/-! An independent client of the whole original eight-node evaluation square. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalEvaluationCommutingParameter
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
  (h : p ≫ v = q ≫ w)

/-- A client constructs the entire actual scalar evaluation family at any spectrum level. -/
noncomputable def evaluationSquareFamily (n : ℕ) :
    C(unitInterval × (unitInterval × (prespectrum (globalModel.obj (op C))).space n),
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :=
  (prespectrumSimplexFamily (InputCommutingSimplex.simplex p v q w h) n).comp
    ⟨fun z => (InputCommutingParameter.parameter (z.1, z.2.1), z.2.2), by fun_prop⟩

/-- The client family is the whole original native square, rather than only its four edges. -/
theorem evaluationSquareFamily_native (n : ℕ) :
    evaluationSquareFamily p v q w h n =
      (InputCommutingSquare.square p v q w h).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, s, x⟩
  exact InputCommutingParameter.native p v q w h n r s x

/-- Every point of the finite scalar carrier fixes the actual original spectrum basepoint. -/
theorem full_scalar_point (n : ℕ) (z : StdSimplex ℝ (Fin 8)) :
    prespectrumSimplexFamily (InputCommutingSimplex.simplex p v q w h) n
        (z, (prespectrum (globalModel.obj (op C))).point n) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).point n :=
  prespectrumSimplexFamily_point (InputCommutingSimplex.simplex p v q w h) n z

/-- The whole evaluated square fixes its point at every value of both native parameters. -/
theorem evaluationSquareFamily_point (n : ℕ) (r s : unitInterval) :
    evaluationSquareFamily p v q w h n
        (r, (s, (prespectrum (globalModel.obj (op C))).point n)) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).point n :=
  full_scalar_point p v q w h n (InputCommutingParameter.parameter (r, s))

/-- The original prespectrum structure time stays independent of both square coordinates. -/
theorem evaluationSquareFamily_structure (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum (globalModel.obj (op C))).space n) :
    evaluationSquareFamily p v q w h (n + 1)
        (r, (s, (prespectrum (globalModel.obj (op C))).structureMap n x t)) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).structureMap n
        (evaluationSquareFamily p v q w h n (r, (s, x))) t :=
  prespectrumSimplexFamily_structure (InputCommutingSimplex.simplex p v q w h) n
    (InputCommutingParameter.parameter (r, s)) x t

/-- The independent client observes the original loop time separately from the scalar square. -/
theorem evaluationSquareFamily_zero_loop (r s t : unitInterval)
    (x : Path (stagePoint 0 (globalModel.obj (op C)))
      (stagePoint 0 (globalModel.obj (op C)))) :
    (show Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen A)))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen A))) from
      evaluationSquareFamily p v q w h 0 (r, (s, x))) t =
        stageSimplexBarycentric (InputCommutingSimplex.simplex p v q w h) 0
          (InputCommutingParameter.parameter (r, s), x t) :=
  prespectrumSimplexFamily_zero_apply (InputCommutingSimplex.simplex p v q w h)
    (InputCommutingParameter.parameter (r, s)) x t

end Consumer.GlobalEvaluationCommutingParameter
