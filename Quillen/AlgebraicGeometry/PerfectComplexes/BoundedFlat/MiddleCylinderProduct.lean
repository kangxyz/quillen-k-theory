/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PolynomialMovingFamily

/-! The independently moving original middle cylinder under coefficient composition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMComponents
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

abbrev coefficientSource := BinaryNormalizationSimplex.sourceMap
  (coefficientMap P v) (coefficientMap P u)
abbrev coefficientNodes := BassH0Merge.binaryNodes (coefficientMap P v) (coefficientMap P u)

/-- Literal realized composition of the original coefficient triangle and Bass projection path. -/
def middleSimplex := CommonReferenceProduct.simplex (coefficientSource P u v)
  (fun i ↦ (coefficientNodes P u v i).1) (fun i ↦ (coefficientNodes P u v i).2)
  (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
  (fun i ↦ (BassProjectionPath.nodes P c i).2)

/-- Both geometric times remain independent in the genuine realization-product parameter. -/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 z.1, BassProjectionPath.parameter z.2), by fun_prop⟩

/-- The node-form binary family retains the entire original normalization triangle. -/
theorem coefficient_simplex_original :
    ModelSimplex.ofIsos (coefficientSource P u v)
      (fun i ↦ (coefficientNodes P u v i).1) (fun i ↦ (coefficientNodes P u v i).2) =
      BinaryNormalizationSimplex.simplex (coefficientMap P v) (coefficientMap P u) := by
  unfold BinaryNormalizationSimplex.simplex
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j f
    fin_cases i <;> fin_cases j <;> rfl

/-- Original coefficient composition retains the complete native binary track at every level. -/
theorem coefficient_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos (coefficientSource P u v)
        (fun i ↦ (coefficientNodes P u v i).1) (fun i ↦ (coefficientNodes P u v i).2)) n
      (binaryPath (k := 2) 0 1 2 r, x) =
      (boundedFlatCoefficientCompositionHomotopy P u v).level n (r, x) := by
  rw [coefficient_simplex_original]
  exact BinaryNormalizationSimplex.native_path (coefficientMap P v) (coefficientMap P u) n r x

/-- The whole middle product retains the actual Bass comparison on the original moving cylinder. -/
theorem middle_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P u v) n (middleParameter.{u} (r, t), x) =
    (boundedFlatCoefficientBassSquareComparison P c).map n
      (HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)) n
        (t, (boundedFlatCoefficientCompositionHomotopy P u v).level n (r, x))) := by
  refine (CommonReferenceProduct.prespectrum_comp (coefficientSource P u v)
    (fun i ↦ (coefficientNodes P u v i).1) (fun i ↦ (coefficientNodes P u v i).2)
    (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
    (fun i ↦ (BassProjectionPath.nodes P c i).2) n x
    (binaryPath (k := 2) 0 1 2 r) (BassProjectionPath.parameter t)).trans ?_
  change prespectrumSimplexFamily (BassProjectionPath.simplex P c) n
    (BassProjectionPath.parameter t,
      prespectrumSimplexFamily
        (ModelSimplex.ofIsos (coefficientSource P u v)
          (fun i ↦ (coefficientNodes P u v i).1) (fun i ↦ (coefficientNodes P u v i).2)) n
        (binaryPath (k := 2) 0 1 2 r, x)) = _
  rw [coefficient_native, BassProjectionPath.native]
  rfl

end Quillen.PerfectComplexes.BassMComponents
