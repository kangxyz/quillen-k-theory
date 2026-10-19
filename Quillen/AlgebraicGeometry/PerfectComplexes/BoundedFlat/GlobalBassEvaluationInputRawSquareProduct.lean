/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNormalizationPrismNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex

/-!
# The actual raw square at a moving evaluation input

The original two-node evaluation comparison and five-node raw geometric square form their
literal categorical product. Its complete native family retains the two independent times,
including the original reverse-forward square clock and the independent level-zero loop.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawSquareProduct
open GlobalSectionChangeIndex InputNormalizationPrism
variable {X Y Z T U : Scheme.{u}}
  (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w) (a : Z ⟶ U)

/-- Every original square vertex keeps its genuine polynomial-source Model arrow. -/
def squareVertices := fun i : Fin 5 => (NativeSquareFiveSimplex.nodes p v q w h i).1

/-- Both original binary normalization references retain the actual commuting-square transport. -/
def squareAnchors := fun i : Fin 5 => (NativeSquareFiveSimplex.nodes p v q w h i).2

/-- The original square factor is retained as an entire Model simplex. -/
theorem square_simplex :
    ModelSimplex.ofIsos (NativeSquareFiveSimplex.source p v)
      (squareVertices p v q w h) (squareAnchors p v q w h) =
    NativeSquareFiveSimplex.simplex p v q w h := rfl

/-- Ten actual composite vertices retain the original independent evaluation and square factors. -/
def simplex :=
  CommonReferenceProduct.simplex (firstSource a) (firstVertices a) (firstAnchors a)
    (NativeSquareFiveSimplex.source p v) (squareVertices p v q w h) (squareAnchors p v q w h)

/-- The full product parameter keeps the original evaluation and square times independent. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 10)) :=
  ⟨fun z => Quillen.SimplexGrid.parameter.{u} 1 4
    ((edge (k := 1) 0 1) z.1, NativeSquareFiveSimplex.parameter z.2), by fun_prop⟩

/-- The original evaluation-source row retains the entire raw square path. -/
theorem parameter_evaluation_zero (s : unitInterval) :
    parameter.{u} (0, s) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 1 4 0).toOrderHom
        (NativeSquareFiveSimplex.parameter s) := by
  change Quillen.SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) 0, NativeSquareFiveSimplex.parameter s) = _
  rw [Path.source]
  exact Quillen.SimplexGrid.parameter_row 1 4 0 _

/-- The evaluated target row retains the same original raw square path without reparametrization. -/
theorem parameter_evaluation_one (s : unitInterval) :
    parameter.{u} (1, s) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 1 4 1).toOrderHom
        (NativeSquareFiveSimplex.parameter s) := by
  change Quillen.SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) 1, NativeSquareFiveSimplex.parameter s) = _
  rw [Path.target]
  exact Quillen.SimplexGrid.parameter_row 1 4 1 _

/-- The source of the reverse-forward square keeps the complete actual evaluation edge. -/
theorem parameter_square_zero (t : unitInterval) :
    parameter.{u} (t, 0) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 1 4 2).toOrderHom
        ((edge (k := 1) 0 1) t) := by
  change Quillen.SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) t, NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source]
  exact Quillen.SimplexGrid.parameter_column 1 4 2 _

/-- The square's target keeps the distinct original raw suffix throughout evaluation. -/
theorem parameter_square_one (t : unitInterval) :
    parameter.{u} (t, 1) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 1 4 4).toOrderHom
        ((edge (k := 1) 0 1) t) := by
  change Quillen.SimplexGrid.parameter 1 4
    ((edge (k := 1) 0 1) t, NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target]
  exact Quillen.SimplexGrid.parameter_column 1 4 4 _

private def squareFamily (n : ℕ) :=
  (prespectrumSimplexFamily (NativeSquareFiveSimplex.simplex p v q w h) n).comp
    (⟨fun z => (NativeSquareFiveSimplex.parameter z.1, z.2), by fun_prop⟩ :
      C(unitInterval × (prespectrum (modelOf (boundedFlatPerfectWaldhausen Z))).space n, _))

private theorem square_whole (n : ℕ) :
    squareFamily p v q w h n =
      (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  exact NativeSquareFiveSimplex.native p v q w h n s x

/-- The original square time and moving evaluation input retain their separate coordinates. -/
def movingParameter (n : ℕ) :
    C((unitInterval × unitInterval) × (prespectrum (globalModel.obj (op U))).space n,
      unitInterval × (prespectrum (modelOf (boundedFlatPerfectWaldhausen Z))).space n) :=
  ⟨fun z => (z.1.2, (evaluationComparison a).level n (z.1.1, z.2)), by fun_prop⟩

/-- The original ten-node product is evaluated as one jointly continuous two-time family. -/
def nativeFamily (n : ℕ) :=
  (prespectrumSimplexFamily (simplex p v q w h a) n).comp
    (⟨fun z => (parameter.{u+1} z.1, z.2), by fun_prop⟩ :
      C((unitInterval × unitInterval) × (prespectrum (globalModel.obj (op U))).space n, _))

private theorem model_whole (n : ℕ) :
    nativeFamily p v q w h a n = (squareFamily p v q w h n).comp (movingParameter a n) := by
  apply ContinuousMap.ext
  rintro ⟨⟨t, s⟩, x⟩
  exact (CommonReferenceProduct.prespectrum_comp
    (firstSource a) (firstVertices a) (firstAnchors a)
    (NativeSquareFiveSimplex.source p v) (squareVertices p v q w h) (squareAnchors p v q w h)
    n x ((edge (k := 1) 0 1) t) (NativeSquareFiveSimplex.parameter s)).trans
    ((congrArg (fun S => prespectrumSimplexFamily S n
      (NativeSquareFiveSimplex.parameter s,
        prespectrumSimplexFamily (firstSimplex a) n ((edge (k := 1) 0 1) t, x)))
      (square_simplex p v q w h)).trans
      (congrArg (fun y => prespectrumSimplexFamily
        (NativeSquareFiveSimplex.simplex p v q w h) n (NativeSquareFiveSimplex.parameter s, y))
        (first_native a n t x)))

/-- The whole original raw square acts on every point of the actual moving evaluation family. -/
theorem whole_native (n : ℕ) :
    nativeFamily p v q w h a n =
      ((boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n).comp
        (movingParameter a n) :=
  (model_whole p v q w h a n).trans
    (congrArg (fun F => F.comp (movingParameter a n)) (square_whole p v q w h n))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawSquareProduct
