/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MVertexParameter

/-! Whole original first M stage, including zero level and independent structure time. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMVertex
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The complete first M stage has the literal original native value at every pair of parameters. -/
theorem native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassMVertexOrder.parameter.{u} (r, t), x) =
    (BassMComponents.originalM P u v).level n
      (lower r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [BassMVertexOrder.parameter_plus]
    change prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassMVertexOrder.plusFace.toOrderHom _, x) = _
    rw [prespectrumSimplexFamily_face, plus_face]
    exact BassMComponents.plus_cell_native P u v n r s x
  · rw [BassMVertexOrder.parameter_middle]
    change prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassMVertexOrder.middleFace.toOrderHom _, x) = _
    rw [prespectrumSimplexFamily_face, middle_face]
    exact BassMComponents.middle_cell_native P u v n r s x
  · rw [BassMVertexOrder.parameter_minus]
    change prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassMVertexOrder.minusFace.toOrderHom _, x) = _
    rw [prespectrumSimplexFamily_face, minus_face]
    exact BassMComponents.minus_cell_native P u v n r s x

/-- The original based point is fixed at every scalar point of the complete first stage. -/
theorem point (n : ℕ) (r t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) n
      (BassMVertexOrder.parameter.{u} (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n _

/-- Both first-stage scalar times remain independent of the original structure coordinate. -/
theorem structure_time (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (BassMVertexOrder.parameter.{u} (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, a)))).structureMap n x z) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n
          (BassMVertexOrder.parameter.{u} (r, t), x)) z :=
  prespectrumSimplexFamily_structure (simplex P u v) n _ x z

end Quillen.PerfectComplexes.BassMVertex
