/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionPath
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition

/-! The full prescribed Laurent-composition cylinder face in one actual product simplex. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassLaurentBottomFace
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The Laurent coefficient scheme map induced by `v`. -/
abbrev firstMap := coefficientMap P ((laurentUnderFunctor R).map v)
/-- The Laurent coefficient scheme map induced by `u`. -/
abbrev secondMap := coefficientMap P ((laurentUnderFunctor R).map u)
/-- The source model map of the binary normalization triangle for the two Laurent coefficient
maps. -/
abbrev source := BinaryNormalizationSimplex.sourceMap (firstMap P v) (secondMap P u)

/-- The source, intermediate, and target model maps of the Laurent binary normalization
triangle. -/
def vertices : Fin 3 →
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj c)))) :=
  ![source P u v,
    BinaryNormalizationSimplex.intermediateMap (firstMap P v) (secondMap P u),
    BinaryNormalizationSimplex.targetMap (firstMap P v) (secondMap P u)]

/-- The identity, first-step, and total references from the source to the three Laurent
vertices. -/
def references : ∀ i, (source P u v).functor ≅ (vertices P u v i).functor :=
  Fin.cases (Iso.refl _)
    (Fin.cases (BinaryNormalizationSimplex.first (firstMap P v) (secondMap P u))
      (Fin.cases (BinaryNormalizationSimplex.total (firstMap P v) (secondMap P u))
        (fun i ↦ Fin.elim0 i)))

/-- Actual composition of the five-vertex Bass projection diagram and Laurent binary triangle. -/
def simplex : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))) 14 :=
  CommonReferenceProduct.simplex
    (BassProjectionPath.source P a) (fun i ↦ (BassProjectionPath.nodes P a i).1)
    (fun i ↦ (BassProjectionPath.nodes P a i).2)
    (source P u v) (vertices P u v) (references P u v)

/-- Both geometric times stay independent in the actual realized grid parameter. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 15)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The fixed original Laurent-composition homotopy is the native binary path, with its
literal endpoint casts and its two original normalization pieces. -/
theorem laurent_native (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos (source P u v)
      (vertices P u v) (references P u v)) n (binaryPath (k := 2) 0 1 2 r, x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P u v).level n (r, x) :=
  BinaryNormalizationSimplex.native_path (firstMap P v) (secondMap P u) n r x

/-- The complete prescribed bottom face of the original Bass interior cube, for every original
level, both independent times and every original overlap input. -/
theorem native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (parameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  refine (CommonReferenceProduct.prespectrum_comp
    (BassProjectionPath.source P a) (fun i ↦ (BassProjectionPath.nodes P a i).1)
    (fun i ↦ (BassProjectionPath.nodes P a i).2)
    (source P u v) (vertices P u v) (references P u v) n x
    (BassProjectionPath.parameter t) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  change prespectrumSimplexFamily (ModelSimplex.ofIsos (source P u v)
      (vertices P u v) (references P u v)) n
    (binaryPath (k := 2) 0 1 2 r,
      prespectrumSimplexFamily (BassProjectionPath.simplex P a) n
        (BassProjectionPath.parameter t, x)) = _
  rw [BassProjectionPath.native P a n t x, laurent_native]
  rfl

end Quillen.PerfectComplexes.BassLaurentBottomFace
