/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassReindexedScalarEdges
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPausedChart
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCarrier

/-!
# The original source-composition row in the polynomial sheet

The inverse original binary total changes the complete eighteen-node reference. On the
ordered source row it cancels its own total and leaves literal postcomposition of the
original binary nodes. The whole binary path and its prescribed terminal half pause are
retained, including the actual polynomial-pair specialization and its native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceAttachment
open BassH0Merge BassH1Join CommonReferenceNerve

/-- The complete source-side row has the original ordered labels `2, 3, 11`. -/
def sourceFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨CoefficientMovingSquareRows.sourceSide,
    CoefficientMovingSquareRows.side_rows_monotone 0⟩

/-- The original two-half binary path is followed by its literal terminal half pause. -/
def pausedBinaryParameter : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 3))
    (StdSimplex.single 2) :=
  (binaryPath 0 1 2).trans (Path.refl (StdSimplex.single 2))

/-- The ordered face carries the entire original source path, at the same speed. -/
theorem source_parameter (r : I) :
    StdSimplex.map sourceFace.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
      DoubleSquareScalarPaths.sourceChart r :=
  BassSupportOrder.map_any_binary sourceFace.toOrderHom 0 1 2 r

/-- The prescribed paused side is the whole face path, including its terminal constant half. -/
theorem paused_side_face (r : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 1) =
      StdSimplex.map sourceFace.toOrderHom (pausedBinaryParameter r) := by
  change collapsed (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter)
    (r, 1) = _
  rw [collapsed_right_path]
  exact (map_trans_values (StdSimplex.map sourceFace.toOrderHom)
    (binaryPath (k := 2) 0 1 2) (Path.refl (StdSimplex.single 2))
    DoubleSquareScalarPaths.sourceChart (Path.refl (StdSimplex.single 11))
    source_parameter (fun _ ↦ by
      simp only [Path.refl_apply, StdSimplex.map_single]
      rfl) r).symm

section Rectangle
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The literal binary-pair reference followed by the actual final scheme map. -/
abbrev sourceReference := BinaryNormalizationSimplex.sourceMap q p ≫ normalizedMap c

/-- The full original normalization total is inverted, without replacing either reference. -/
def sourceAnchor : (sourceReference p q c).functor ≅
    (NormalizedTripleSimplex.sourceMap c q p).functor :=
  (BinaryNormalizationSimplex.total c (q ≫ p)).symm

/-- All eighteen nodes are retained in the literal source-composition reference. -/
def sourceNodes : Fin 18 → Node (sourceReference p q c) :=
  fun i ↦ anchorNode (sourceAnchor p q c)
    (CoefficientMovingSquareRows.nodes p q p' q' a b c hp hq i)

/-- The full source row cancels only the original total with its inverse. -/
theorem source_nodes (i : Fin 3) :
    sourceNodes p q p' q' a b c hp hq (CoefficientMovingSquareRows.sourceSide i) =
      postcompNode (normalizedMap c) (binaryNodes q p i) := by
  unfold sourceNodes
  rw [CoefficientMovingSquareRows.source_side_nodes, anchor_post_node]
  simp only [sourceAnchor, Iso.symm_self_id, postReferenceNode, postcompNode, Iso.refl_trans]

/-- The equality is on the complete ordered face, before any native evaluation. -/
theorem source_face_parameter (z : StdSimplex ℝ (Fin 3)) :
    parameter (sourceReference p q c) (sourceNodes p q p' q' a b c hp hq)
        (StdSimplex.map sourceFace.toOrderHom z) =
      mapParameter (postcompNode (normalizedMap c))
        (parameter (BinaryNormalizationSimplex.sourceMap q p) (binaryNodes q p) z) := by
  rw [parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter (sourceReference p q c) N z)
  funext i
  exact source_nodes p q p' q' a b c hp hq i

/-- The original source path remains the literal postcomposition of the binary path. -/
theorem source_path_parameter (r : I) :
    parameter (sourceReference p q c) (sourceNodes p q p' q' a b c hp hq)
        (DoubleSquareScalarPaths.sourceChart r) =
      mapParameter (postcompNode (normalizedMap c))
        (parameter (BinaryNormalizationSimplex.sourceMap q p) (binaryNodes q p)
          (binaryPath (k := 2) 0 1 2 r)) := by
  rw [← source_parameter]
  exact source_face_parameter p q p' q' a b c hp hq _

/-- The original paused square attaches along the binary path with its terminal pause. -/
theorem paused_square_source (r : I) :
    parameter (sourceReference p q c) (sourceNodes p q p' q' a b c hp hq)
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 1)) =
      mapParameter (postcompNode (normalizedMap c))
        (parameter (BinaryNormalizationSimplex.sourceMap q p) (binaryNodes q p)
          (pausedBinaryParameter r)) := by
  rw [paused_side_face]
  exact source_face_parameter p q p' q' a b c hp hq _
end Rectangle

section Coefficients
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The entire original polynomial pair path in its own reference, with the fixed pause. -/
def polynomialPausedPath : C(I, |nerve (Codiscrete
    (Node (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)))|) :=
  (parameter (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)))).comp
    pausedBinaryParameter.toContinuousMap

/-- The first half retains the entire original polynomial composition at its native speed. -/
theorem polynomialPausedPath_lower (r : I) :
    polynomialPausedPath P p q (lower r) =
      CoefficientBassSpanCompositionReference.coefficientPath P
        ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q) r := by
  change parameter _ _ (pausedBinaryParameter (lower r)) = _
  rw [pausedBinaryParameter, path_lower]
  rfl

/-- The whole terminal half is the literal original final value. -/
theorem polynomialPausedPath_upper (r : I) :
    polynomialPausedPath P p q (upper r) =
      CoefficientBassSpanCompositionReference.coefficientPath P
        ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q) 1 := by
  change parameter _ _ (pausedBinaryParameter (upper r)) = parameter _ _ _
  rw [pausedBinaryParameter, path_upper]
  exact congrArg
    (parameter (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((polynomialUnderFunctor R).map p))))
    (binaryPath (k := 2) 0 1 2).target.symm

/-- Every native level recovers the original polynomial pair homotopy followed by `refl`. -/
theorem polynomialPausedPath_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    pointwisePrespectrumFamily
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) n
        (polynomialPausedPath P p q r) x =
      ((boundedFlatCoefficientCompositionHomotopy P
        ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q)).trans
          (Quillen.LoopPrespectrum.Homotopy.refl _)).level n (r, x) := by
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [polynomialPausedPath_lower, Quillen.LoopPrespectrum.Homotopy.trans_lower_cell]
    exact CoefficientBassSpanCompositionReference.coefficientPath_native P
      ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q) n t x
  · rw [polynomialPausedPath_upper, Quillen.LoopPrespectrum.Homotopy.trans_upper_cell]
    exact (CoefficientBassSpanCompositionReference.coefficientPath_native P
      ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q) n 1 x).trans
        ((boundedFlatCoefficientCompositionHomotopy P
          ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q)).at_one n x)

/-- The complete actual chart-side row becomes literal postcomposition in the single sheet. -/
theorem sheet_source_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)
        (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q
          (CoefficientMovingSquareRows.sourceSide i)) =
      postcompNode (BassMWholeNerve.coefficientModel P (β.app c))
        (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
          (coefficientMap P ((polynomialUnderFunctor R).map p)) i) :=
  source_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (coefficientMap P ((laurentUnderFunctor R).map p))
    (coefficientMap P ((laurentUnderFunctor R).map q))
    (coefficientMap P (β.app a)) (coefficientMap P (β.app b)) (coefficientMap P (β.app c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm i

/-- The whole paused chart attaches to the genuine polynomial pair with its original clock. -/
theorem sheetFamily_right (r : I) :
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 1) =
      mapParameter (postcompNode (BassMWholeNerve.coefficientModel P (β.app c)))
        (polynomialPausedPath P p q r) := by
  change mapParameter
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
    (parameter (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)
      (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q)
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 1))) = _
  rw [mapParameter_parameter, paused_side_face, parameter_face]
  change parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
    (fun i ↦ CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)
      (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q (sourceFace.toOrderHom i)))
    (pausedBinaryParameter r) =
      mapParameter (postcompNode (BassMWholeNerve.coefficientModel P (β.app c)))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
          (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((polynomialUnderFunctor R).map p))) (pausedBinaryParameter r))
  rw [mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q) N
    (pausedBinaryParameter r))
  funext i
  exact sheet_source_nodes P β p q i

/-- The same seam is the actual realized attachment used by the ordinary cylinder. -/
theorem sheetFamily_right_attaching (r : I) :
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 1) =
      SSet.toTop.map (CutOpenCarrier.attaching
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
        (BassMWholeNerve.coefficientModel P (β.app c))
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q ≫
          BassMWholeNerve.coefficientModel P (β.app c)) (Iso.refl _))
        (polynomialPausedPath P p q r) := by
  rw [sheetFamily_right]
  let F := CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
  let J := BassMWholeNerve.coefficientModel P (β.app c)
  change mapParameter (postcompNode J) (polynomialPausedPath P p q r) =
    mapParameter (attachPostcompNode F J (F ≫ J) (Iso.refl _))
      (polynomialPausedPath P p q r)
  have h : attachPostcompNode F J (F ≫ J) (Iso.refl _) = postcompNode J := by
    funext N
    simp only [attachPostcompNode, postcompNode, Iso.refl_trans]
  rw [h]
end Coefficients

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceAttachment
