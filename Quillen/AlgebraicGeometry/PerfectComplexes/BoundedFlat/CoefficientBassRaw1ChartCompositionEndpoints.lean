/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1ChartCompositionCells

/-! Complete chart columns at the original Laurent-composition endpoints. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- Every original five-node chart column retains the selected complete Laurent reference. -/
def columnNodes (j : Fin 3) (i : Fin 5) : Node (reference P β f p q) :=
  CommonReferenceProduct.node (reference P β f p q) (chartReference P β f)
    (CoefficientBassLaurentCompositionCarrier.reference P p q) (Iso.refl _)
    (chartNodes P β f i) (CoefficientBassLaurentCompositionCarrier.nodes P p q j)

/-- The initial composition endpoint retains the entire original chart-square clock. -/
theorem family_zero (t : I) : family P β f p q (0, t) =
    parameter (reference P β f p q) (columnNodes P β f p q 0)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [family, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Path.source, FiniteParameter.parameter_vertex]
  dsimp only [chartFamily, ContinuousMap.comp_apply, Path.coe_toContinuousMap]
  rw [mapParameter_parameter]
  rfl

/-- The terminal composition endpoint retains the same full chart-square clock. -/
theorem family_one (t : I) : family P β f p q (1, t) =
    parameter (reference P β f p q) (columnNodes P β f p q 2)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [family, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [Path.target, FiniteParameter.parameter_vertex]
  dsimp only [chartFamily, ContinuousMap.comp_apply, Path.coe_toContinuousMap]
  rw [mapParameter_parameter]
  rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
