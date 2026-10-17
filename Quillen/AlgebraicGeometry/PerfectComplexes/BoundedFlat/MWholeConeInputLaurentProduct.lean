/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentCompositionCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetConeNative

/-! The original H0 surface followed by Laurent composition in the ordinary input cap. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputLaurentProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassH0Merge BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The first height half retains the original H0 target reference. -/
abbrev surfaceReference := reference P b (E ≫ normalizedMap (coefficientMap P p))

/-- Its Laurent composition factor is the original binary reference, without reanchoring. -/
abbrev productReference := surfaceReference P p E ≫
  CoefficientBassLaurentCompositionCarrier.reference P q w

/-- Each node includes both original full natural isomorphisms in their actual product order. -/
def productNode (N : Node (surfaceReference P p E)) (j : Fin 3) :
    Node (productReference P p q w E) :=
  CommonReferenceProduct.node (productReference P p q w E) (surfaceReference P p E)
    (CoefficientBassLaurentCompositionCarrier.reference P q w) (Iso.refl _) N
    (CoefficientBassLaurentCompositionCarrier.nodes P q w j)

/-- The unchanged binary clock acts on every point of the whole H0 target nerve. -/
def product : C(|parameterSSet (surfaceReference P p E)| × I,
    |parameterSSet (productReference P p q w E)|) :=
  (FiniteParameter.parameter (surfaceReference P p E) (productReference P p q w E)
    (productNode P p q w E)).comp
    { toFun := fun z ↦ (z.1, binaryPath (k := 2) 0 1 2 z.2)
      continuous_toFun := continuous_fst.prodMk
        ((binaryPath (k := 2) 0 1 2).continuous.comp continuous_snd) }

/-- The composition, original tree, and original H0 time remain independent coordinates. -/
def family : C(I × (FourEdgeTree.space E (normalizedMap (polynomialProjection P a)) × I),
    |parameterSSet (productReference P p q w E)|) :=
  (product P p q w E).comp
    { toFun := fun z ↦ (FourEdge.TargetCone.surface P p E z.2, z.1)
      continuous_toFun :=
        ((FourEdge.TargetCone.surface P p E).continuous.comp continuous_snd).prodMk
          continuous_fst }

/-- The lower H0 row retains the whole original Laurent coefficient action. -/
theorem family_source (r : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) :
    family P p q w E (r, (z, 0)) = product P p q w E
      (FourEdge.TargetCone.laurent P p E (SSet.toTop.map (FourEdge.beta P a E) z), r) := by
  change product P p q w E (FourEdge.TargetCone.surface P p E (z, 0), r) = _
  rw [FourEdge.TargetCone.surface_zero]

/-- The upper H0 row is exactly beta of the prescribed target tree map. -/
theorem family_target (r : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) :
    family P p q w E (r, (z, 1)) = product P p q w E
      (SSet.toTop.map (FourEdge.beta P b (E ≫ normalizedMap (coefficientMap P p)))
        (FourEdge.TargetSpan.treeMap P p E z), r) := by
  change product P p q w E (FourEdge.TargetCone.surface P p E (z, 1), r) = _
  rw [FourEdge.TargetCone.surface_one]

/-- The initial composition edge is the induced full node map on the entire H0 surface. -/
theorem family_zero
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) (s : I) :
    family P p q w E (0, (z, s)) =
      mapParameter (fun N ↦ productNode P p q w E N 0)
        (FourEdge.TargetCone.surface P p E (z, s)) := by
  change FiniteParameter.parameter _ _ (productNode P p q w E)
    (FourEdge.TargetCone.surface P p E (z, s), binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, FiniteParameter.parameter_vertex]

/-- The terminal composition edge retains the last original full binary node. -/
theorem family_one
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a))) (s : I) :
    family P p q w E (1, (z, s)) =
      mapParameter (fun N ↦ productNode P p q w E N 2)
        (FourEdge.TargetCone.surface P p E (z, s)) := by
  change FiniteParameter.parameter _ _ (productNode P p q w E)
    (FourEdge.TargetCone.surface P p E (z, s), binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target, FiniteParameter.parameter_vertex]

/-- Product evaluation is the original Laurent composition on every genuine input. -/
theorem product_native (n : ℕ) (r : I) (y : |parameterSSet (surfaceReference P p E)|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (productReference P p q w E) n (product P p q w E (y, r)) x =
      (boundedFlatCoefficientLaurentCompositionHomotopy P q w).level n
        (r, pointwisePrespectrumFamily (surfaceReference P p E) n y x) := by
  have hp := CoefficientBassSeedTargetChartNative.finite_product_native
    (surfaceReference P p E) (CoefficientBassLaurentCompositionCarrier.reference P q w)
    (productReference P p q w E) (Iso.refl _)
    (CoefficientBassLaurentCompositionCarrier.nodes P q w) n y
    (binaryPath (k := 2) 0 1 2 r) x
  have h := CoefficientBassLaurentCompositionCarrier.family_native P q w n r
    (pointwisePrespectrumFamily (surfaceReference P p E) n y x)
  rw [← pointwisePrespectrumFamily_eq_compact] at h
  dsimp only [CoefficientBassLaurentCompositionCarrier.family, ContinuousMap.comp_apply] at h
  rw [pointwisePrespectrumFamily_parameter] at h
  exact hp.trans h

/-- All native levels recover the original Laurent K half on the unchanged H0 input. -/
theorem family_native (n : ℕ) (r s : I)
    (z : FourEdgeTree.space E (normalizedMap (polynomialProjection P a)))
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (productReference P p q w E) n
      (family P p q w E (r, (z, s))) x =
      (boundedFlatCoefficientLaurentCompositionHomotopy P q w).level n
        (r, (boundedFlatCoefficientBassComparisonHomotopy P p).level n
          (s, FourEdgeTree.nativeEval E (normalizedMap (polynomialProjection P a)) n z x)) := by
  change pointwisePrespectrumFamily (productReference P p q w E) n
    (product P p q w E (FourEdge.TargetCone.surface P p E (z, s), r)) x = _
  rw [product_native, FourEdge.TargetCone.surface_native]

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputLaurentProduct
