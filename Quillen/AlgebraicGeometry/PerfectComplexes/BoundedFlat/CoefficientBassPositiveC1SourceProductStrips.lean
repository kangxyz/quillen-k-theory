/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceUnitProduct
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomPositiveColumn
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassSharedNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1BoundarySeam
public import Quillen.Topology.Realization.SimplexGridColumn

/-! Source-positive and source-unit product strips with their complete reference-node faces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1SourceProductStrips
open CommonReferenceNerve CommonReferenceProduct LaurentUnitReferenceSpecialization
open CoefficientBassPositiveC1SourceUnitProduct
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Nine source-positive/Laurent-binary nodes, in the original source-first product order. -/
def positiveNineNodes (i : Fin 9) : Node (BassOverlap.commonReference P p q) :=
  node (BassOverlap.commonReference P p q) (BassProjectionPath.source P a)
    (BassLaurentBottomFace.source P p q) (BassBottomCommonFamily.referenceIso P p q)
    (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a)
      ((SimplexGrid.indexEquiv 2 2).symm i).1)
    (laurentNodes P p q ((SimplexGrid.indexEquiv 2 2).symm i).2)

/-- Each of the nine nodes is literally its full node in the canonical fifteen-node family. -/
theorem positiveNine_bottom_nodes (i j : Fin 3) :
    positiveNineNodes P p q (SimplexGrid.index 2 2 (i, j)) =
      BassBottomCommonFamily.bottomNodes P p q
        (SimplexGrid.index 4 2 (Fin.castAdd 2 i, j)) := by
  unfold positiveNineNodes BassBottomCommonFamily.bottomNodes
    CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [SimplexGrid.decode_index, SimplexGrid.decode_index]
  dsimp only
  rw [BassH0Merge.projection_plus_nodes P (a := a) i]; rfl

/-- The ordinary start row retains the exact bottom anchor and all Laurent references. -/
theorem positiveNine_start_nodes (j : Fin 3) :
    positiveNineNodes P p q (SimplexGrid.index 2 2 (0, j)) =
      positiveStartNodes P p q j := by
  unfold positiveNineNodes
  rw [SimplexGrid.decode_index]; rfl

/-- Composition time is first; the source-positive binary time is second. -/
def positiveParameter :
    C(I × I, |nerve (Codiscrete (Node (BassOverlap.commonReference P p q)))|) :=
  (parameter (BassOverlap.commonReference P p q) (positiveNineNodes P p q)).comp
    ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 2
      (binaryPath (k := 2) 0 1 2 z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The second sheet uses the actual common-unit reference action on every full node. -/
def shiftedPositiveParameter :
    C(I × I, |nerve (Codiscrete (Node (BassOverlap.commonReference P p q)))|) :=
  (mapParameter (reanchor (commonUnit P p q))).comp (positiveParameter P p q)

/-- The forward source-unit edge and Laurent binary time are independent coordinates. -/
def unitParameter :
    C(I × I, |nerve (Codiscrete (Node (BassOverlap.commonReference P p q)))|) :=
  (parameter (BassOverlap.commonReference P p q) (unitSixNodes P p q)).comp
    ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 1 2
      (edge (k := 1) 0 1 z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The whole ordinary start path, before any native evaluation. -/
theorem positive_start (r : I) :
    positiveParameter P p q (r, 0) =
      parameter (BassOverlap.commonReference P p q) (positiveStartNodes P p q)
        (binaryPath (k := 2) 0 1 2 r) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 2
    (binaryPath (k := 2) 0 1 2 0, binaryPath (k := 2) 0 1 2 r)) = _
  rw [Path.source, SimplexGrid.parameter_row, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (positiveNine_start_nodes P p q))

/-- The lower unit rail is the entire ordinary positive start path. -/
theorem unit_lower (r : I) :
    unitParameter P p q (r, 0) = positiveParameter P p q (r, 0) := by
  rw [positive_start]
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
    (edge (k := 1) 0 1 0, binaryPath (k := 2) 0 1 2 r)) = _
  rw [Path.source, SimplexGrid.parameter_row, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (unitSix_lower_nodes P p q))

/-- The upper unit rail is the entire separately shifted positive start path. -/
theorem unit_upper (r : I) :
    unitParameter P p q (r, 1) = shiftedPositiveParameter P p q (r, 0) := by
  change unitParameter P p q (r, 1) =
    mapParameter (reanchor (commonUnit P p q)) (positiveParameter P p q (r, 0))
  rw [positive_start, mapParameter_parameter]
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
    (edge (k := 1) 0 1 1, binaryPath (k := 2) 0 1 2 r)) = _
  rw [Path.target, SimplexGrid.parameter_row, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (unitSix_upper_nodes P p q))

/-- The positive terminal rail is the full terminal source row of the canonical bottom family. -/
theorem positive_end (r : I) :
    positiveParameter P p q (r, 1) =
      parameter (BassOverlap.commonReference P p q)
        (fun j ↦ BassBottomCommonFamily.bottomNodes P p q
          (SimplexGrid.index 4 2 ((2 : Fin 5), j)))
        (binaryPath (k := 2) 0 1 2 r) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 2
    (binaryPath (k := 2) 0 1 2 1, binaryPath (k := 2) 0 1 2 r)) = _
  rw [Path.target, SimplexGrid.parameter_row, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (positiveNine_bottom_nodes P p q 2))

/-- The entire source face of the unit rectangle is its two full source-column nodes. -/
theorem unit_source (s : I) :
    unitParameter P p q (0, s) =
      parameter (BassOverlap.commonReference P p q)
        (fun i ↦ unitSixNodes P p q (SimplexGrid.index 1 2 (i, 0)))
        (edge (k := 1) 0 1 s) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
    (edge (k := 1) 0 1 s, binaryPath (k := 2) 0 1 2 0)) = _
  rw [Path.source, SimplexGrid.parameter_column, parameter_face]; rfl

/-- The entire target face of the unit rectangle is its two full target-column nodes. -/
theorem unit_target (s : I) :
    unitParameter P p q (1, s) =
      parameter (BassOverlap.commonReference P p q)
        (fun i ↦ unitSixNodes P p q (SimplexGrid.index 1 2 (i, 2)))
        (edge (k := 1) 0 1 s) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
    (edge (k := 1) 0 1 s, binaryPath (k := 2) 0 1 2 1)) = _
  rw [Path.target, SimplexGrid.parameter_column, parameter_face]; rfl

/-- The positive endpoint row has the three exact original chart references. -/
theorem positive_end_chart_nodes (j : Fin 3) :
    BassBottomCommonFamily.bottomNodes P p q (SimplexGrid.index 4 2 ((2 : Fin 5), j)) =
      BassOverlap.chartOverlapNodes P p q (underToLaurent R)
        (laurentPlus_projection P c) (Fin.natAdd 15 j) := by
  fin_cases j
  · exact (BassReferenceMerge.plus_source_node P p q).symm
  · exact (BassReferenceMerge.plus_intermediate_node P p q).symm
  · exact (BassReferenceMerge.plus_target_node P p q).symm

/-- The whole terminal positive rail, with its original binary clock and full chart references. -/
theorem positive_end_chart (r : I) :
    positiveParameter P p q (r, 1) =
      parameter (BassOverlap.commonReference P p q)
        (fun j ↦ BassOverlap.chartOverlapNodes P p q (underToLaurent R)
          (laurentPlus_projection P c) (Fin.natAdd 15 j))
        (binaryPath (k := 2) 0 1 2 r) := by
  rw [positive_end]
  exact congrArg (fun N : Fin 3 → Node (BassOverlap.commonReference P p q) ↦
    parameter (BassOverlap.commonReference P p q) N (binaryPath (k := 2) 0 1 2 r))
    (funext (positive_end_chart_nodes P p q))

/-- The shifted terminal rail retains the same three nodes under the actual common unit. -/
theorem shifted_positive_end_chart (r : I) :
    shiftedPositiveParameter P p q (r, 1) =
      parameter (BassOverlap.commonReference P p q)
        (fun j ↦ reanchor (commonUnit P p q)
          (BassOverlap.chartOverlapNodes P p q (underToLaurent R)
            (laurentPlus_projection P c) (Fin.natAdd 15 j)))
        (binaryPath (k := 2) 0 1 2 r) := by
  change mapParameter (reanchor (commonUnit P p q)) (positiveParameter P p q (r, 1)) = _
  rw [positive_end_chart, mapParameter_parameter]

/-- Ordered inclusion of the original three terminal chart nodes. -/
def terminalChartFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.natAdd 15, fun _ _ h ↦ Nat.add_le_add_left h 15⟩

/-- The ordinary strip attaches to the whole original chart edge, with its literal clock. -/
theorem positive_chart_seam (r : I) :
    positiveParameter P p q (r, 1) =
      CoefficientBassPositiveC1BoundaryLift.chartParameter P p q (r, 0) := by
  rw [positive_end_chart]
  change parameter _ _ (binaryPath (k := 2) 0 1 2 r) =
    parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))
  rw [DoubleSquareScalarPaths.coefficientPausedSquareParameter_left]
  have h := map_binaryPath terminalChartFace 0 1 2 r
  change StdSimplex.map terminalChartFace.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
    DoubleSquareScalarPaths.targetChart r at h
  rw [← h, parameter_face]
  exact congrArg (fun N ↦ parameter (BassOverlap.commonReference P p q) N
    (binaryPath (k := 2) 0 1 2 r)) (funext (fun j ↦ by
      change BassOverlap.chartOverlapNodes P p q (underToLaurent R)
        (laurentPlus_projection P c) (Fin.natAdd 15 j) =
        BassOverlap.chartOverlapNodes P p q (underToLaurent R)
          (laurentPlus_projection P c) (Fin.natAdd 15 j)
      rfl))

/-- The separate shifted attachment follows from full reference transport on the whole edge. -/
theorem shifted_positive_chart_seam (r : I) :
    shiftedPositiveParameter P p q (r, 1) =
      mapParameter (reanchor (commonUnit P p q))
        (CoefficientBassPositiveC1BoundaryLift.chartParameter P p q (r, 0)) := by
  exact congrArg (mapParameter (reanchor (commonUnit P p q))) (positive_chart_seam P p q r)

/-- The complete positive source column keeps its full three product nodes. -/
theorem positive_source (s : I) :
    positiveParameter P p q (0, s) =
      parameter (BassOverlap.commonReference P p q)
        (fun i ↦ positiveNineNodes P p q (SimplexGrid.index 2 2 (i, 0)))
        (binaryPath (k := 2) 0 1 2 s) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 2
    (binaryPath (k := 2) 0 1 2 s, binaryPath (k := 2) 0 1 2 0)) = _
  rw [Path.source, SimplexGrid.parameter_column, parameter_face]; rfl

/-- The complete positive target column keeps its full three product nodes. -/
theorem positive_target (s : I) :
    positiveParameter P p q (1, s) =
      parameter (BassOverlap.commonReference P p q)
        (fun i ↦ positiveNineNodes P p q (SimplexGrid.index 2 2 (i, 2)))
        (binaryPath (k := 2) 0 1 2 s) := by
  change parameter _ _ (SimplexGrid.parameter.{u + 1} 2 2
    (binaryPath (k := 2) 0 1 2 s, binaryPath (k := 2) 0 1 2 1)) = _
  rw [Path.target, SimplexGrid.parameter_column, parameter_face]; rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveC1SourceProductStrips
