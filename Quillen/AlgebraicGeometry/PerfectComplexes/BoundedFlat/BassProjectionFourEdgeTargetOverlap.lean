/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ScalarEdges
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReferencePointwise
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluationCells

/-!
# The prescribed target coefficient surface on the four ordinary overlap cells

The second finite factor is the existing 31-node H0 diagram, with its original collapsed
pasting parameter. The first factor is an entire coefficient reference nerve. All four
original quarter restrictions agree before native evaluation. The two polynomial attachment
rows remain separate full-reference obligations, on their own polynomial input model.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open CommonReferenceNerve ProjectionRectangleParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The literal composite reference of the unchanged H0 diagram. -/
abbrev reference := E ≫ BassH0Diagram.reference P f

/-- Compose full source nodes with the existing H0 nodes, without changing either anchor. -/
def nodes (N : CommonReferenceNerve.Node E) (j : Fin 31) :
    CommonReferenceNerve.Node (reference P f E) :=
  ⟨N.1 ≫ (BassH0Diagram.nodes P f j).1,
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      (N.2.prod (BassH0Diagram.nodes P f j).2)⟩

/-- The entire overlap carries the original two independent H0 coordinates. -/
def overlap : C(|nerve (Codiscrete (CommonReferenceNerve.Node E))| × (I × I),
    |nerve (Codiscrete (CommonReferenceNerve.Node (reference P f E)))|) :=
  (FiniteParameter.parameter E (reference P f E) (nodes P f E)).comp
    ⟨fun z ↦ (z.1, BassH0Diagram.parameter z.2), by fun_prop⟩

/-- Every finite source chain retains the original product parameter. -/
theorem overlap_characteristic {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node E)
    (z : StdSimplex ℝ (Fin (k + 1))) (s t : I) :
    overlap P f E (CommonReferenceNerve.parameter E N z, (s, t)) =
      CommonReferenceNerve.parameter (reference P f E)
        (FiniteParameter.gridNodes E (reference P f E) (nodes P f E) N)
        (SimplexGrid.parameter.{u + 1} k 30 (z, BassH0Diagram.parameter (s, t))) :=
  FiniteParameter.parameter_characteristic E (reference P f E) (nodes P f E)
    N z (BassH0Diagram.parameter (s, t))

/-- Native evaluation is exactly the original B surface on an arbitrary finite source chain. -/
theorem finite_native {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node E)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (s t : I)
    (x : (prespectrum V).space n) :
    prespectrumFamily (reference P f E)
      (FiniteParameter.gridNodes E (reference P f E) (nodes P f E) N) n
      (SimplexGrid.parameter.{u + 1} k 30 (z, BassH0Diagram.parameter (s, t)), x) =
      (boundedFlatCoefficientBassComparisonHomotopy P f).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
          (t, prespectrumFamily E N n (z, x))) := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (CommonReferenceProduct.simplex E (fun i ↦ (N i).1) (fun i ↦ (N i).2)
      (BassH0Diagram.reference P f) (fun j ↦ (BassH0Diagram.nodes P f j).1)
      (fun j ↦ (BassH0Diagram.nodes P f j).2)) n
    (SimplexGrid.parameter.{u + 1} k 30 (z, BassH0Diagram.parameter (s, t)), x) = _
  rw [CommonReferenceProduct.prespectrum_comp]
  exact BassH0Diagram.native P f n s t _

/-- All degrees and arbitrary whole-nerve points recover the original native B. -/
theorem overlap_native (n : ℕ) (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s t : I)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P f E) n (overlap P f E (y, (s, t))) x =
      (boundedFlatCoefficientBassComparisonHomotopy P f).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
          (t, pointwisePrespectrumFamily E n y x)) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter E y
  rw [← hz, overlap_characteristic, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact finite_native P f E N n z s t x

/-- The left whole face is the unchanged positive H0 chart row. -/
theorem overlap_left (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    overlap P f E (y, (s, 0)) =
      FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, L BassH0Diagram.plusFace s) := by
  change FiniteParameter.parameter _ _ _ (y, BassH0Diagram.parameter (s, 0)) = _
  rw [BassH0Diagram.parameter_left]

/-- The right whole face retains the inverse chart's separate original row. -/
theorem overlap_right (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    overlap P f E (y, (s, 1)) =
      FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, L BassH0Diagram.minusFace s) := by
  change FiniteParameter.parameter _ _ _ (y, BassH0Diagram.parameter (s, 1)) = _
  rw [BassH0Diagram.parameter_right]

/-- A cell restriction retains the literal original quarter clock. -/
def cell (clock : C(I, I)) : C(|nerve (Codiscrete (CommonReferenceNerve.Node E))| × (I × I),
    |nerve (Codiscrete (CommonReferenceNerve.Node (reference P f E)))|) :=
  (overlap P f E).comp ⟨fun z ↦ (z.1, (z.2.1, clock z.2.2)), by fun_prop⟩

/-- The continuous version of the prescribed edge-one-to-two clock. -/
def clock12 : C(I, I) := ⟨FourEdgeTree.time12, by unfold FourEdgeTree.time12; fun_prop⟩
/-- The continuous version of the prescribed edge-zero-to-one clock. -/
def clock01 : C(I, I) := ⟨FourEdgeTree.time01, by unfold FourEdgeTree.time01; fun_prop⟩
/-- The continuous version of the prescribed edge-zero-to-three clock. -/
def clock03 : C(I, I) := ⟨FourEdgeTree.time03, by unfold FourEdgeTree.time03; fun_prop⟩
/-- The continuous version of the prescribed edge-three-to-four clock. -/
def clock34 : C(I, I) := ⟨FourEdgeTree.time34, by unfold FourEdgeTree.time34; fun_prop⟩

theorem seam_one (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    cell P f E clock01 (y, (s, 1)) = cell P f E clock12 (y, (s, 0)) := by
  change overlap P f E (y, (s, FourEdgeTree.time01 1)) =
    overlap P f E (y, (s, FourEdgeTree.time12 0))
  rw [FourEdgeTree.time01_one]

theorem seam_zero (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    cell P f E clock03 (y, (s, 0)) = cell P f E clock01 (y, (s, 0)) := by
  change overlap P f E (y, (s, FourEdgeTree.time03 0)) =
    overlap P f E (y, (s, FourEdgeTree.time01 0))
  rw [FourEdgeTree.time03_zero]

theorem seam_three (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    cell P f E clock34 (y, (s, 0)) = cell P f E clock03 (y, (s, 1)) := by
  change overlap P f E (y, (s, FourEdgeTree.time34 0)) =
    overlap P f E (y, (s, FourEdgeTree.time03 1))
  rw [FourEdgeTree.time34_zero]

theorem cell12_endpoint (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    cell P f E clock12 (y, (s, 1)) = overlap P f E (y, (s, 0)) := by
  change overlap P f E (y, (s, FourEdgeTree.time12 1)) = _
  rw [FourEdgeTree.time12_one]

theorem cell34_endpoint (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    cell P f E clock34 (y, (s, 1)) = overlap P f E (y, (s, 1)) := by
  change overlap P f E (y, (s, FourEdgeTree.time34 1)) = _
  rw [FourEdgeTree.time34_one]

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
