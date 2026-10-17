/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPausedChart
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentCompositionCarrier

/-!
# The original Laurent-composition row in the polynomial sheet

The lower edge of the prescribed paused chart is the unchanged three-node Laurent
composition path, precomposed by the actual chart at its source. Its complete reference
transport is the original sheet anchor followed by the last source transport and the
original right-first binary normalization. The proof uses the actual ordered target row
of the eighteen-node moving square before any native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialLowerAttachment
open BassH0Merge CommonReferenceNerve

/-- The complete target-side row has the original ordered labels `15, 16, 17`. -/
def targetFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨CoefficientMovingSquareRows.targetSide,
    CoefficientMovingSquareRows.side_rows_monotone 1⟩

/-- The ordered face carries the whole original Laurent binary path at its original speed. -/
theorem target_parameter (r : I) :
    StdSimplex.map targetFace.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
      DoubleSquareScalarPaths.targetChart r :=
  BassSupportOrder.map_any_binary targetFace.toOrderHom 0 1 2 r

/-- The prescribed right-side pause leaves this entire opposite side unchanged. -/
theorem paused_side_face (r : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0) =
      StdSimplex.map targetFace.toOrderHom (binaryPath (k := 2) 0 1 2 r) := by
  change collapsed (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter)
    (r, 0) = _
  rw [collapsed_left_path]
  exact (target_parameter r).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete lower reference uses only the original sheet and last-triple transports. -/
def lowerAnchor :
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q).functor ≅
      (BassMWholeNerve.coefficientModel P (β.app a) ≫
        CoefficientBassLaurentCompositionCarrier.reference P p q).functor :=
  CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q ≪≫
    (DoubleSquareCommonSimplex.lastSourceIso
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((laurentUnderFunctor R).map p))
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P (β.app a)) (coefficientMap P (β.app b))
      (coefficientMap P (β.app c))
      (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm ≪≫
      NormalizedTripleSimplex.rightFirst
        (coefficientMap P ((laurentUnderFunctor R).map q))
        (coefficientMap P ((laurentUnderFunctor R).map p))
        (coefficientMap P (β.app a)))

/-- Every complete lower node is the original Laurent node precomposed by the source chart. -/
theorem sheet_target_nodes (i : Fin 3) :
    CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)
        (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q
          (CoefficientMovingSquareRows.targetSide i)) =
      CommonReferenceProduct.reanchor (lowerAnchor P β p q)
        (precompNode (BassMWholeNerve.coefficientModel P (β.app a))
          (CoefficientBassLaurentCompositionCarrier.nodes P p q i)) := by
  refine (congrArg
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
    (CoefficientMovingSquareRows.target_side_nodes
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((laurentUnderFunctor R).map p))
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P (β.app a)) (coefficientMap P (β.app b))
      (coefficientMap P (β.app c))
      (coefficientMap_naturality P β p).symm
      (coefficientMap_naturality P β q).symm i)).trans ?_
  simp only [CommonReferenceProduct.reanchor, preReferenceNode, precompNode,
    lowerAnchor, Iso.trans_assoc]
  rfl

/-- The whole lower edge is the unchanged Laurent binary family in this exact sheet reference. -/
theorem sheetFamily_lower (r : I) :
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 0) =
      mapParameter (fun N ↦ CommonReferenceProduct.reanchor (lowerAnchor P β p q)
        (precompNode (BassMWholeNerve.coefficientModel P (β.app a)) N))
        (CoefficientBassLaurentCompositionCarrier.family P p q r) := by
  change mapParameter
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q))
    (parameter (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)
      (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q)
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) = _
  rw [mapParameter_parameter, paused_side_face, parameter_face]
  change parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
    (fun i ↦ CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)
      (CoefficientBassRaw1PolynomialPausedChart.nodes P β p q (targetFace.toOrderHom i)))
    (binaryPath (k := 2) 0 1 2 r) =
      mapParameter (fun N ↦ CommonReferenceProduct.reanchor (lowerAnchor P β p q)
        (precompNode (BassMWholeNerve.coefficientModel P (β.app a)) N))
        (parameter (CoefficientBassLaurentCompositionCarrier.reference P p q)
          (CoefficientBassLaurentCompositionCarrier.nodes P p q)
          (binaryPath (k := 2) 0 1 2 r))
  rw [mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q) N
    (binaryPath (k := 2) 0 1 2 r))
  funext i
  exact sheet_target_nodes P β p q i

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialLowerAttachment
