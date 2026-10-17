/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1ChartCompositionProduct
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialLowerAttachment
public import Quillen.Topology.Realization.SimplexGridBoundary

/-! Full-reference terminal join for the original chart-square/composition product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- The terminal square node followed by the unchanged three Laurent nodes. -/
def terminalNodes (j : Fin 3) : Node (reference P β f p q) :=
  CommonReferenceProduct.node (reference P β f p q)
    (chartReference P β f) (CoefficientBassLaurentCompositionCarrier.reference P p q)
    (Iso.refl _) (chartNodes P β f 4) (CoefficientBassLaurentCompositionCarrier.nodes P p q j)

/-- The complete fifteen-node family restricts to the literal terminal row. -/
theorem family_terminal_row (r : I) :
    family P β f p q (r, 1) = parameter (reference P β f p q)
      (terminalNodes P β f p q) (binaryPath (k := 2) 0 1 2 r) := by
  dsimp only [family, ContinuousMap.comp_apply, ContinuousMap.coe_mk, chartFamily,
    Path.coe_toContinuousMap]
  rw [NativeSquareFiveSimplex.parameter.target, FiniteParameter.parameter_characteristic,
    SimplexGrid.parameter_row, parameter_face]
  apply congrArg (fun N ↦ parameter (reference P β f p q) N
    (binaryPath (k := 2) 0 1 2 r))
  funext j
  exact FiniteParameter.gridNodes_index _ _ _ _ 4 j

/-- The actual polynomial coefficient input at the second half of the old Bass map. -/
abbrev polynomialInput := BassMWholeNerve.coefficientModel P
  ((polynomialUnderFunctor R).map f)

/-- The terminal full square anchor followed by the original lower-sheet anchor. -/
def midpointIso : (reference P β f p q).functor ≅
    (polynomialInput P f ≫
      CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q).functor :=
  isoWhiskerRight (chartNodes P β f 4).2
    (CoefficientBassLaurentCompositionCarrier.reference P p q).functor ≪≫
    isoWhiskerLeft (polynomialInput P f).functor
      (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q).symm

/-- The entire terminal row agrees before evaluation with source-precomposition of the sheet. -/
theorem terminal_node (j : Fin 3) :
    terminalNodes P β f p q j =
      CommonReferenceProduct.reanchor (midpointIso P β f p q)
        (precompNode (polynomialInput P f)
          (CommonReferenceProduct.reanchor
            (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
            (precompNode (BassMWholeNerve.coefficientModel P (β.app b))
              (CoefficientBassLaurentCompositionCarrier.nodes P p q j)))) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [terminalNodes, CommonReferenceProduct.node, CommonReferenceProduct.reanchor,
    precompNode, midpointIso, Iso.trans_hom, Iso.refl_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Category.id_comp, Category.assoc]
  simp only [Iso.symm_hom, Iso.inv_hom_id_app_assoc]
  rfl

/-- The two original cap halves have exactly the same full reference along their midpoint. -/
theorem family_terminal (r : I) :
    family P β f p q (r, 1) =
      mapParameter (fun N ↦ CommonReferenceProduct.reanchor (midpointIso P β f p q)
        (precompNode (polynomialInput P f) N))
        (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 0)) := by
  rw [family_terminal_row, CoefficientBassRaw1PolynomialLowerAttachment.sheetFamily_lower]
  dsimp only [CoefficientBassLaurentCompositionCarrier.family, ContinuousMap.comp_apply]
  rw [mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter (reference P β f p q) N
    (binaryPath (k := 2) 0 1 2 r))
  funext j
  exact terminal_node P β f p q j

end Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
