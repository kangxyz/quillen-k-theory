/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointRows

/-! Complete original five-node endpoint rows of the paused polynomial cap. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairEndpointReferences
open CommonReferenceNerve CoefficientMovingSquareRows BassH1Join BassH0Merge

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
/-- The coefficient map induced by the polynomial image of `p`. -/
abbrev pp := coefficientMap P ((polynomialUnderFunctor R).map p)
/-- The coefficient map induced by the polynomial image of `q`. -/
abbrev pq := coefficientMap P ((polynomialUnderFunctor R).map q)
/-- The coefficient map induced by the Laurent image of `p`. -/
abbrev lp := coefficientMap P ((laurentUnderFunctor R).map p)
/-- The coefficient map induced by the Laurent image of `q`. -/
abbrev lq := coefficientMap P ((laurentUnderFunctor R).map q)
/-- The coefficient map induced by the chart component `β.app a`. -/
abbrev ca := coefficientMap P (β.app a)
/-- The coefficient map induced by the chart component `β.app b`. -/
abbrev cb := coefficientMap P (β.app b)
/-- The coefficient map induced by the chart component `β.app c`. -/
abbrev cc := coefficientMap P (β.app c)

/-- The entire outer chart row retains its original complete normalization anchor. -/
def outerNodes (i : Fin 5) := CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q) (anchorNode (outerAnchor (pp
    P p) (pq P q) (lp P p) (lq P q) (ca P β (a := a)) (cb P β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm)
      (NativeSquareFiveSimplex.nodes ((lq P q) ≫ (lp P p)) (ca P β (a := a))
        (cc P β (c := c)) ((pq P q) ≫ (pp P p))
        (DoubleSquareTrack.total_eq (pp P p) (pq P q) (lp P p) (lq P q) (ca P β (a := a)) (cb P
    β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm) i))

/-- Equality of all five full reference nodes, before any evaluation. -/
theorem outer_nodes (i : Fin 5) :
    CoefficientBassRaw1PolynomialPairEndpointRows.rowNodes P β p q 0 i =
      outerNodes P β p q i := by
  have h := outer_row_nodes (pp P p) (pq P q) (lp P p) (lq P q) (ca P β (a := a)) (cb P β (b :=
    b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm i
  exact congrArg (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)) h

/-- The entire first chart row retains its original complete normalization anchor. -/
def firstNodes (i : Fin 5) := CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q) (postReferenceNode
    (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)
      (normalizedMap (lq P q)) (firstAnchor (pp P p) (pq P q) (lp P p) (lq P q) (ca P β (a :=
    a)) (cb P β (b := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm)
      (NativeSquareFiveSimplex.nodes (lp P p) (ca P β (a := a))
        (cb P β (b := b)) (pp P p) (coefficientMap_naturality P β p) i))

/-- Equality of all five full reference nodes, before any evaluation. -/
theorem first_nodes (i : Fin 5) :
    CoefficientBassRaw1PolynomialPairEndpointRows.rowNodes P β p q 1 i =
      firstNodes P β p q i := by
  have h := first_row_nodes (pp P p) (pq P q) (lp P p) (lq P q) (ca P β (a := a)) (cb P β (b :=
    b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm i
  exact congrArg (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)) h

/-- The entire second chart row retains its original complete normalization anchor. -/
def secondNodes (i : Fin 5) := CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q) (preReferenceNode
    (CoefficientBassRaw1PolynomialPausedChart.reference P β p q)
      (normalizedMap (pp P p))
      (secondAnchor (pp P p) (pq P q) (lq P q) (cb P β (b := b))
        (cc P β (c := c)) (coefficientMap_naturality P β q).symm)
      (NativeSquareFiveSimplex.nodes (lq P q) (cb P β (b := b))
        (cc P β (c := c)) (pq P q) (coefficientMap_naturality P β q) i))

/-- Equality of all five full reference nodes, before any evaluation. -/
theorem second_nodes (i : Fin 5) :
    CoefficientBassRaw1PolynomialPairEndpointRows.rowNodes P β p q 2 i =
      secondNodes P β p q i := by
  have h := second_row_nodes (pp P p) (pq P q) (lp P p) (lq P q) (ca P β (a := a)) (cb P β (b
    := b)) (cc P β (c := c))
    (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm i
  exact congrArg (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q)) h

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairEndpointReferences
