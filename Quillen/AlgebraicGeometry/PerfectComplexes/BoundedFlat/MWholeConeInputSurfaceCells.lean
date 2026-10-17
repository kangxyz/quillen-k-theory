/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputIdentityChart
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeOverlap

/-! The unchanged three target-span cells in the whole ordinary input-cap midpoint. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct
open BassProjectionPath.WholeReference

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (p : a ⟶ b)
variable {V : Model.{u + 1}} (E : V ⟶ model P a)
local notation "Ja" => normalizedMap (polynomialProjection P a)

/-- The original two positive quarters become exactly the original whole polynomial square. -/
theorem target_overlap_lower (y : |parameterSSet E|) (s : I) :
    FourEdge.TargetSpan.treeMap P p E (FourEdgeTree.overlap E Ja (y, lower s)) =
      FourEdge.TargetSpan.plusSquare P p E (y, s) := by
  rcases cover (unitInterval.symm s) with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hs : s = unitInterval.symm (lower t) := by rw [ht, unitInterval.symm_symm]
    rw [hs, FourEdgeTree.overlap_quarter01, FourEdge.TargetSpan.treeMap_edge01]
  · have hs : s = unitInterval.symm (upper t) := by rw [ht, unitInterval.symm_symm]
    rw [hs, FourEdgeTree.overlap_quarter12, FourEdge.TargetSpan.treeMap_edge12]
    have hc : lower (unitInterval.symm t) = unitInterval.symm (upper t) := by
      apply Subtype.ext
      change (1 - (t : ℝ)) / 2 = 1 - (((t : ℝ) + 1) / 2)
      ring
    rw [hc]

/-- The middle quarter is the entire original overlap on the coefficient input. -/
theorem target_overlap_middle (y : |parameterSSet E|) (s : I) :
    FourEdge.TargetSpan.treeMap P p E
      (FourEdgeTree.overlap E Ja (y, upper (lower s))) =
      FourEdge.TargetSpan.central P p E (y, s) := by
  rw [FourEdgeTree.overlap_quarter03, FourEdge.TargetSpan.treeMap_edge03]

/-- The final quarter retains the original reversed negative polynomial square. -/
theorem target_overlap_upper (y : |parameterSSet E|) (s : I) :
    FourEdge.TargetSpan.treeMap P p E
      (FourEdgeTree.overlap E Ja (y, upper (upper s))) =
      FourEdge.TargetSpan.minusSquare P p E (y, unitInterval.symm s) := by
  rw [FourEdgeTree.overlap_quarter34, FourEdge.TargetSpan.treeMap_edge34]

local notation "A" => normalizedMap (coefficientMap P p)
local notation "S" => A ≫ BassProjectionPath.source P b
local notation "E₀" => (𝟙 (model P a) ≫ A)

/-- The actual whole target surface is normalized only by the specified identity unitor. -/
def targetSurface : C(I, |parameterSSet S|) :=
  (mapParameter (reanchor (surfaceIdentity P p))).comp
    ((SSet.toTop.map (FourEdge.beta P b E₀)).hom.comp
      ((FourEdge.TargetSpan.treeMap P p (𝟙 (model P a))).comp (overlap P a)))

/-- The first half of the complete target surface is the original positive lower surface. -/
theorem targetSurface_lower (s : I) :
    targetSurface P p (lower s) =
      InputPolynomial.lowerSurface P p (underToLaurent R) (laurentPlus_projection P b) s := by
  change mapParameter _ (SSet.toTop.map _ (FourEdge.TargetSpan.treeMap P p (𝟙 (model P a))
    (FourEdgeTree.overlap _ _ (identityParameter P a, lower s)))) = _
  rw [target_overlap_lower]
  change mapParameter _ (SSet.toTop.map (FourEdge.beta P b E₀)
    (SSet.toTop.map (FourEdgeTree.plusVertex E₀ (normalizedMap (polynomialProjection P b)))
      (FourEdge.TargetSpan.polynomialSquare P p (𝟙 (model P a))
        (identityParameter P a, s)))) = _
  rw [← FourEdgeTree.realized_comp, FourEdge.beta_plus]
  exact identity_chart_parameter P p (underToLaurent R) (laurentPlus_projection P b) s

/-- The last quarter is the original negative lower surface at its unchanged reverse clock. -/
theorem targetSurface_upper (s : I) :
    targetSurface P p (upper (upper s)) =
      InputPolynomial.lowerSurface P p (underToLaurentInvert R) (laurentMinus_projection P b)
        (unitInterval.symm s) := by
  change mapParameter _ (SSet.toTop.map _ (FourEdge.TargetSpan.treeMap P p (𝟙 (model P a))
    (FourEdgeTree.overlap _ _ (identityParameter P a, upper (upper s))))) = _
  rw [target_overlap_upper]
  change mapParameter _ (SSet.toTop.map (FourEdge.beta P b E₀)
    (SSet.toTop.map (FourEdgeTree.minusVertex E₀ (normalizedMap (polynomialProjection P b)))
      (FourEdge.TargetSpan.polynomialSquare P p (𝟙 (model P a))
        (identityParameter P a, unitInterval.symm s)))) = _
  rw [← FourEdgeTree.realized_comp, FourEdge.beta_minus]
  exact identity_chart_parameter P p (underToLaurentInvert R) (laurentMinus_projection P b) _

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
