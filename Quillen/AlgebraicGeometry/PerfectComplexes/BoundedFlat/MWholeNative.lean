/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeScalarFaces

/-! Whole original M and the five unchanged original faces in the concrete common native family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole
open BassMWholeOrder
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The entire scalar family evaluates to the literal original M at every level and both times. -/
theorem m_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (mParameter.{u} (r, t), x) =
    (BassMComponents.originalM P u v).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  BassMFamilyTransfer.native P u v (nodes P u v) vertexIndex oldIndex
    (old_nodes P u v) (vertex_nodes P u v) supportOrders indexEqualities n r t x

/-- Every point of the whole common simplex fixes the original native based point. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 140)) :
    prespectrumSimplexFamily (simplex P u v) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n z

/-- Native structure time is independent of every scalar point in the entire common simplex. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 140))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P u v) n z x t

/-- The complete original M family fixes the unchanged based point at every parameter. -/
theorem m_point (n : ℕ) (r t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) n
      (mParameter.{u} (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  family_point P u v n _

/-- Both whole M coordinates remain independent of the original structure coordinate. -/
theorem m_structure (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (mParameter.{u} (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, a)))).structureMap n x z) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (mParameter.{u} (r, t), x)) z :=
  family_structure P u v n _ x z

/-- Every original plus face value is retained in the concrete common simplex. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (plusParameter (r, s), x) =
    (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  BassMFamilyTransfer.plus_native P u v (nodes P u v) vertexIndex oldIndex
    (old_nodes P u v) supportOrders n r s x

/-- Every original minus face value is retained in the concrete common simplex. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (minusParameter (r, s), x) =
    (boundedFlatCoefficientBassCompositionMinusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  BassMFamilyTransfer.minus_native P u v (nodes P u v) vertexIndex oldIndex
    (old_nodes P u v) supportOrders n r s x

/-- Every original bottom face value is retained in the concrete common simplex. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (bottomParameter.{u} (r, t), x) =
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  BassMFamilyTransfer.bottom_native P u v (nodes P u v) vertexIndex oldIndex
    (old_nodes P u v) supportOrders n r t x

/-- Every original h0 face value is retained in the concrete common simplex. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (h0Parameter (s, t), x) =
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
      (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  BassMFamilyTransfer.h0_native P u v (nodes P u v) vertexIndex oldIndex
    (old_nodes P u v) supportOrders n s t x

/-- Every original h1 face value is retained in the concrete common simplex. -/
theorem h1_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (h1Parameter.{u} (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  BassMFamilyTransfer.h1_native P u v (nodes P u v) vertexIndex oldIndex
    (old_nodes P u v) supportOrders n s t x

end Quillen.PerfectComplexes.BassMWhole
