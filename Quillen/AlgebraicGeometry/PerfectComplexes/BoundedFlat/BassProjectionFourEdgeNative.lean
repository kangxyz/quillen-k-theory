/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeRealization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReferencePointwise

/-!
# Native compatibility on the entire original four-edge Bass span

The two polynomial summands and four original cylinders determine the complete set-level
map. Their exact full-reference evaluations recover the original Bass square comparison in
every degree, including degree zero. No global joint-continuity assertion is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)
local notation "F" => reference P a E

/-- Every point of the whole polynomial summand has its original chart-map value. -/
theorem chartMap_native
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (n : ℕ) (y : |parameterSSet (polynomialReference P a E)|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (SSet.toTop.map (chartMap P a E α ha) y) x =
      (prespectrumMap (normalizedMap (coefficientMap P (α.app a)))).map n
        (pointwisePrespectrumFamily (polynomialReference P a E) n y x) :=
  pointwisePrespectrumFamily_attachPostcomp (polynomialReference P a E)
    (normalizedMap (coefficientMap P (α.app a))) F
    (isoWhiskerLeft E.functor (BassMJoin.projectionEndpointIso (c := a) P α ha)) n y x

/-- Native compatibility on the entire positive polynomial summand. -/
theorem beta_native_plus (n : ℕ) (y : |parameterSSet (E ≫ J)|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
        (SSet.toTop.map (beta P a E) (SSet.toTop.map (FourEdgeTree.plusVertex E J) y)) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n (SSet.toTop.map (FourEdgeTree.plusVertex E J) y) x) := by
  rw [← FourEdgeTree.realized_comp, beta_plus, FourEdgeTree.nativeEval_plus]
  calc
    _ = (prespectrumMap (normalizedMap (coefficientMap P ((underToLaurent R).app a)))).map n
        (pointwisePrespectrumFamily (polynomialReference P a E) n y x) :=
      chartMap_native P a E (underToLaurent R) (laurentPlus_projection P a) n y x
    _ = _ := rfl

/-- Native compatibility on the separate inverse polynomial summand. -/
theorem beta_native_minus (n : ℕ) (y : |parameterSSet (E ≫ J)|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
        (SSet.toTop.map (beta P a E) (SSet.toTop.map (FourEdgeTree.minusVertex E J) y)) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n (SSet.toTop.map (FourEdgeTree.minusVertex E J) y) x) := by
  rw [← FourEdgeTree.realized_comp, beta_minus, FourEdgeTree.nativeEval_minus]
  calc
    _ = (prespectrumMap
        (normalizedMap (coefficientMap P ((underToLaurentInvert R).app a)))).map n
        (pointwisePrespectrumFamily (polynomialReference P a E) n y x) :=
      chartMap_native P a E (underToLaurentInvert R) (laurentMinus_projection P a) n y x
    _ = _ := rfl

/-- The complete positive normalization cylinder retains its original quarter clock. -/
theorem beta_native_edge12 (n : ℕ) (y : |parameterSSet E|) (t : unitInterval)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
        (SSet.toTop.map (beta P a E) (FourEdgeTree.realizedEdge
          (FourEdgeTree.edge12 E J) (y, t))) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge12 E J) (y, t)) x) := by
  have hr : FourEdgeTree.realizedEdge (edgeMap P a E 1 2) (y, t) =
      FiniteParameter.parameter E F (nodes P a E)
        (y, SimplexParameters.edge (k := 4) 1 2 t) :=
    edgeMap_realization P a E 1 2 (by decide) y t
  rw [← FourEdgeTree.realizedEdge_comp, beta_edge12, hr, pointwise_edge12,
    FourEdgeTree.nativeEval_edge12]; rfl

/-- The complete positive geometric cylinder retains its original quarter clock. -/
theorem beta_native_edge01 (n : ℕ) (y : |parameterSSet E|) (t : unitInterval)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
        (SSet.toTop.map (beta P a E) (FourEdgeTree.realizedEdge
          (FourEdgeTree.edge01 E J) (y, t))) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge01 E J) (y, t)) x) := by
  have hr : FourEdgeTree.realizedEdge (edgeMap P a E 0 1) (y, t) =
      FiniteParameter.parameter E F (nodes P a E)
        (y, SimplexParameters.edge (k := 4) 0 1 t) :=
    edgeMap_realization P a E 0 1 (by decide) y t
  rw [← FourEdgeTree.realizedEdge_comp, beta_edge01, hr, pointwise_edge01,
    FourEdgeTree.nativeEval_edge01]; rfl

/-- The complete inverse geometric cylinder retains its original quarter clock. -/
theorem beta_native_edge03 (n : ℕ) (y : |parameterSSet E|) (t : unitInterval)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
        (SSet.toTop.map (beta P a E) (FourEdgeTree.realizedEdge
          (FourEdgeTree.edge03 E J) (y, t))) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge03 E J) (y, t)) x) := by
  have hr : FourEdgeTree.realizedEdge (edgeMap P a E 0 3) (y, t) =
      FiniteParameter.parameter E F (nodes P a E)
        (y, SimplexParameters.edge (k := 4) 0 3 t) :=
    edgeMap_realization P a E 0 3 (by decide) y t
  rw [← FourEdgeTree.realizedEdge_comp, beta_edge03, hr, pointwise_edge03,
    FourEdgeTree.nativeEval_edge03]; rfl

/-- The complete inverse normalization cylinder retains its original quarter clock. -/
theorem beta_native_edge34 (n : ℕ) (y : |parameterSSet E|) (t : unitInterval)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n
        (SSet.toTop.map (beta P a E) (FourEdgeTree.realizedEdge
          (FourEdgeTree.edge34 E J) (y, t))) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n
          (FourEdgeTree.realizedEdge (FourEdgeTree.edge34 E J) (y, t)) x) := by
  have hr : FourEdgeTree.realizedEdge (edgeMap P a E 3 4) (y, t) =
      FiniteParameter.parameter E F (nodes P a E)
        (y, SimplexParameters.edge (k := 4) 3 4 t) :=
    edgeMap_realization P a E 3 4 (by decide) y t
  rw [← FourEdgeTree.realizedEdge_comp, beta_edge34, hr, pointwise_edge34,
    FourEdgeTree.nativeEval_edge34]; rfl

/-- The actual Laurent map and native span evaluation agree on every whole-tree point. -/
theorem beta_native (n : ℕ) (z : FourEdgeTree.space E J)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (SSet.toTop.map (beta P a E) z) x =
      (boundedFlatCoefficientBassSquareComparison P a).map n
        (FourEdgeTree.nativeEval E J n z x) := by
  exact congrFun (FourEdgeTree.funext_cells E J
    (fun y ↦ pointwisePrespectrumFamily F n (SSet.toTop.map (beta P a E) y) x)
    (fun y ↦ (boundedFlatCoefficientBassSquareComparison P a).map n
      (FourEdgeTree.nativeEval E J n y x))
    (fun y ↦ beta_native_plus P a E n y x)
    (fun y ↦ beta_native_minus P a E n y x)
    (fun y t ↦ beta_native_edge12 P a E n y t x)
    (fun y t ↦ beta_native_edge01 P a E n y t x)
    (fun y t ↦ beta_native_edge03 P a E n y t x)
    (fun y t ↦ beta_native_edge34 P a E n y t x)) z

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
