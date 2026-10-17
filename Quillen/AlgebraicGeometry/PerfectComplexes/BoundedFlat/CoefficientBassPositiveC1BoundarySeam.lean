/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideScalars
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactAttachment

/-!
# The actual paused C1 carrier attachment seam

This lower owner keeps the original full dependent reference nodes, ordered source row,
scalar pause and characteristic-map attachment equality. Its native right-seam consequence
uses only the existing compact attachment evaluator. It does not import the positive-cone
composition or mixed-route owners and does not assume any seam or higher filler.

The namespace and every moved declaration body are unchanged from the original draft.
Exact recovery of the prescribed native support tracks remains in C1BoundaryLift.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1BoundaryLift
open BassH0Merge CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The fixed polynomial reference is the actual precomposed source binary reference. -/
abbrev polynomialReference :=
  BassOverlap.projectionMap P (a := a) ≫ BassMOuterJoin.sideBinarySource P u v

/-- The Laurent reference is exactly the original common overlap reference. -/
abbrev laurentReference := BassOverlap.commonReference P u v

/-- The target is the original positive chart map on the final coefficient fiber. -/
abbrev chartMap := normalizedMap (laurentPlus P c)

/-- The attachment uses the old paused chart's actual normalization reference route. -/
def ordinaryAnchor : (laurentReference P u v).functor ≅
    (polynomialReference P u v ≫ chartMap P (c := c)).functor :=
  BassMOuterJoin.oldSideIso P u v (underToLaurent R) (laurentPlus_projection P c)

/-- Every polynomial node retains its full original precomposition reference. -/
def polynomialNodes (i : Fin 3) : Node (polynomialReference P u v) :=
  precompNode (BassOverlap.projectionMap P (a := a)) (BassMOuterJoin.sideBinaryNodes P u v i)

/-- All eighteen original positive chart nodes are retained without changing their reference. -/
abbrev chartNodes :=
  BassOverlap.chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c)

/-- The ordinary attachment is the actual full-reference postcomposition node function. -/
def ordinaryAttachNode : Node (polynomialReference P u v) → Node (laurentReference P u v) :=
  attachPostcompNode (polynomialReference P u v) (chartMap P (c := c))
    (laurentReference P u v) (ordinaryAnchor P u v)

/-- The used three-node row really is ordered; no nonmonotone chart word is made into a face. -/
def sourceFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨CoefficientMovingSquareRows.sourceSide,
    CoefficientMovingSquareRows.side_rows_monotone 0⟩

/-- The unchanged polynomial composition parameter keeps its terminal half pause. -/
def pausedBinaryParameter : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 3))
    (StdSimplex.single 2) :=
  (binaryPath 0 1 2).trans (Path.refl (StdSimplex.single 2))

/-- The exact polynomial parameter is independent of the native level and input. -/
def polynomialParameter : C(I, |nerve (Codiscrete (Node (polynomialReference P u v)))|) :=
  (parameter (polynomialReference P u v) (polynomialNodes P u v)).comp
    pausedBinaryParameter.toContinuousMap

/-- The whole original paused chart square has its original eighteen-node parameter. -/
def chartParameter : C(I × I, |nerve (Codiscrete (Node (laurentReference P u v)))|) :=
  (parameter (laurentReference P u v) (chartNodes P u v)).comp
    DoubleSquareScalarPaths.coefficientPausedSquareParameter

/-- The source-side equality is between complete dependent nodes, including the reference iso. -/
theorem chart_source_nodes (i : Fin 3) :
    chartNodes P u v (sourceFace.toOrderHom i) =
      ordinaryAttachNode P u v (polynomialNodes P u v i) := by
  have hi : sourceFace.toOrderHom i =
      DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  change BassOverlap.chartOverlapNodes P u v (underToLaurent R)
    (laurentPlus_projection P c) (sourceFace.toOrderHom i) = _
  rw [hi, BassMOuterJoin.old_side_row]
  apply Sigma.ext (Model.Hom.ext rfl)
  apply heq_of_eq
  apply Iso.ext
  ext X
  rfl

/-- Both exact half formulas imply the whole original paused scalar identity. -/
theorem paused_side_face (r : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 1) =
      StdSimplex.map sourceFace.toOrderHom (pausedBinaryParameter r) := by
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [BassMOuterJoin.paused_side_lower, pausedBinaryParameter, path_lower]
    exact (BassSupportOrder.map_any_binary sourceFace.toOrderHom 0 1 2 t).symm
  · rw [BassMOuterJoin.paused_side_upper, pausedBinaryParameter, path_upper]
    simp only [Path.refl_apply, StdSimplex.map_single]
    rfl

/-- The entire original right side attaches in the carrier, before any native evaluation. -/
theorem chart_right_attach (r : I) :
    chartParameter P u v (r, 1) =
      mapParameter (ordinaryAttachNode P u v) (polynomialParameter P u v r) := by
  change parameter (laurentReference P u v) (chartNodes P u v)
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 1)) =
    mapParameter (ordinaryAttachNode P u v)
      (parameter (polynomialReference P u v) (polynomialNodes P u v)
        (pausedBinaryParameter r))
  rw [paused_side_face, parameter_face, mapParameter_parameter]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P u v) ↦
    parameter (laurentReference P u v) N (pausedBinaryParameter r))
    (funext (chart_source_nodes P u v))

/-- The original first half retains the literal binary normalization speed. -/
theorem polynomialParameter_lower (r : I) :
    polynomialParameter P u v (lower r) =
      parameter (polynomialReference P u v) (polynomialNodes P u v)
        (binaryPath (k := 2) 0 1 2 r) := by
  change parameter _ _ (pausedBinaryParameter (lower r)) = _
  rw [pausedBinaryParameter, path_lower]

/-- The complete second half is the original terminal node, including its shared endpoint. -/
theorem polynomialParameter_upper (r : I) :
    polynomialParameter P u v (upper r) =
      parameter (polynomialReference P u v) (polynomialNodes P u v)
        (StdSimplex.single 2) := by
  change parameter _ _ (pausedBinaryParameter (upper r)) = _
  rw [pausedBinaryParameter, path_upper]
  rfl

/-- The native right seam is a consequence of the proved full carrier attachment equation. -/
theorem chart_right_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P u v) (chartParameter P u v)
      n ((r, 1), x) =
    (prespectrumMap (chartMap P (c := c))).map n
      (compactPrespectrumFamily (polynomialReference P u v) (polynomialParameter P u v)
        n (r, x)) := by
  have h := (chart_right_attach P u v r).trans
    (mapParameter_parameter (ordinaryAttachNode P u v) (polynomialNodes P u v)
      (pausedBinaryParameter r))
  rw [compactPrespectrumFamily_eq_simplex _ _
    (fun i ↦ ordinaryAttachNode P u v (polynomialNodes P u v i)) (r, 1)
    (pausedBinaryParameter r) h n x,
    compactPrespectrumFamily_eq_simplex _ _ (polynomialNodes P u v) r
      (pausedBinaryParameter r) rfl n x]
  exact prespectrumFamily_attachPostcomp (polynomialReference P u v) (chartMap P (c := c))
    (laurentReference P u v) (ordinaryAnchor P u v) (polynomialNodes P u v)
    n (pausedBinaryParameter r) x

end Quillen.PerfectComplexes.CoefficientBassPositiveC1BoundaryLift
