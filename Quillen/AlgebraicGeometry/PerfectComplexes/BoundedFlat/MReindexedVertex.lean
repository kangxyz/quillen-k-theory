/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReindexedH1Cells

/-! Exact transfer of every point of the original whole first M stage. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) {k : ℕ}
  (N : Fin (k + 1) → BassOverlap.Node P u v)
  (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))
  (hv : ∀ i, N (f i) = BassMVertex.nodes P u v i) (o : SupportOrders f g)

include hv o in
/-- All three component families retain every scalar point through their 14 proved supports. -/
theorem vertex_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map f (BassMVertexOrder.parameter.{u} (r, t)), x) =
    prespectrumSimplexFamily (BassMVertex.simplex P u v) n
      (BassMVertexOrder.parameter.{u} (r, t), x) := by
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [BassMVertexOrder.parameter_plus]
    change prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map f (StdSimplex.map BassMVertexOrder.plusIndex
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s))), x) = _
    change _ = prespectrumSimplexFamily (BassMVertex.simplex P u v) n
      (StdSimplex.map BassMVertexOrder.plusIndex
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s)), x)
    obtain ⟨i, z, hz⟩ := BassMPrimitiveSupport.moving_support (r, s)
    rw [← hz]
    exact composed_supported_value (BassOverlap.commonReference P u v) (BassMVertex.nodes P u v)
      N f hv BassMVertexOrder.plusIndex (BassPrimitiveSupport.rectangleFace i)
      (BassMVertexOrder.plusFace.toOrderHom.monotone.comp
        (BassPrimitiveSupport.rectangleFace i).toOrderHom.monotone)
      (o.vertexPlus i) n z x
  · rw [BassMVertexOrder.parameter_middle]
    change prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map f (StdSimplex.map BassMVertexOrder.middleIndex
        (BassMComponents.middleParameter.{u} (r, s))), x) = _
    change _ = prespectrumSimplexFamily (BassMVertex.simplex P u v) n
      (StdSimplex.map BassMVertexOrder.middleIndex (BassMComponents.middleParameter.{u} (r, s)), x)
    obtain ⟨i, j, z, hz⟩ := BassMPrimitiveSupport.middle_support.{u} r s
    rw [← hz]
    exact composed_supported_value (BassOverlap.commonReference P u v) (BassMVertex.nodes P u v)
      N f hv BassMVertexOrder.middleIndex (BassMPrimitiveSupport.middleEdgePairFace i j)
      (BassMVertexOrder.middleFace.toOrderHom.monotone.comp
        (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom.monotone)
      (o.vertexMiddle i j) n z x
  · rw [BassMVertexOrder.parameter_minus]
    change prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map f (StdSimplex.map BassMVertexOrder.minusIndex
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm s))), x) = _
    change _ = prespectrumSimplexFamily (BassMVertex.simplex P u v) n
      (StdSimplex.map BassMVertexOrder.minusIndex
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm s)), x)
    obtain ⟨i, z, hz⟩ := BassMPrimitiveSupport.moving_support (r, unitInterval.symm s)
    rw [← hz]
    exact composed_supported_value (BassOverlap.commonReference P u v) (BassMVertex.nodes P u v)
      N f hv BassMVertexOrder.minusIndex (BassPrimitiveSupport.rectangleFace i)
      (BassMVertexOrder.minusFace.toOrderHom.monotone.comp
        (BassPrimitiveSupport.rectangleFace i).toOrderHom.monotone)
      (o.vertexMinus i) n z x

include hv o in
/-- The whole first M stage retains all levels, original inputs, and native time speeds. -/
theorem vertex_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map f (BassMVertexOrder.parameter.{u} (r, t)), x) =
    (BassMComponents.originalM P u v).level n
      (lower r, Quillen.LoopPrespectrum.HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (vertex_value P u v N f g hv o n r t x).trans (BassMVertex.native P u v n r t x)

end Quillen.PerfectComplexes.BassMFamilyTransfer
