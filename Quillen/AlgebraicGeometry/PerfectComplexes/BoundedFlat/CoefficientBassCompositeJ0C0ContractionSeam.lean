/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0C0SeedAlignment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0PairedNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Polynomial

/-!
# Both actual C0 source contraction rails

The terminal polynomial movement node is identified with its complete coefficient reference.
The two cylinder paths then agree at every contraction time, retaining their distinct tips.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0C0ContractionSeam
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0PolynomialEndpoints
private theorem parameter_vertex {V W : Model.{v}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → Node F) (i : Fin (k + 1)) :
    parameter F N (StdSimplex.single i) = nodePoint F (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) =
      StdSimplex.single i := by
    rw [StdSimplex.map_single]
    rfl
  rw [← hm, parameter_face]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The terminal polynomial point retains the full direct-composite coefficient reference. -/
theorem movement_terminal : CoefficientBassCompositeJ0Polynomial.movement P p q 1 =
    nodePoint _ (sourceNullNode P p
      q) := by
  change parameter _ (CoefficientBassCompositeJ0Polynomial.nodes P p q)
    (NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target, parameter_vertex,
    CoefficientBassCompositeJ0Polynomial.terminal_coefficient_node, source_node]

/-- The entire ordinary source contraction equals the actual rebased new cone path. -/
theorem contractionMinus_newCone (s : I) :
    CoefficientBassCompositeJ0C0SeedAlignment.toJ0 P p q
      (CoefficientBassPositiveC0CarrierSeed.contractionMinus P
        p q (s, 0)) =
      CoefficientBassCompositeJ0PairedNull.newConeMinus P p q s := by
  rw [(CoefficientBassPositiveC0CarrierSeed.source_contractions P
    p q s).1]
  change CoefficientBassPositiveC0CarrierSeed.minusCylinder P
    p q
      (nodePoint _ (sourceNullNode P _ _), s) =
    CoefficientBassPositiveC0CarrierSeed.minusCylinder P
      p q
        (CoefficientBassCompositeJ0Polynomial.movement P p q 1, s)
  rw [movement_terminal]

/-- The entire shifted source contraction keeps the second cylinder and its own tip. -/
theorem contractionPlus_newCone (s : I) :
    CoefficientBassCompositeJ0C0SeedAlignment.toJ0 P p q
      (CoefficientBassPositiveC0CarrierSeed.contractionPlus P
        p q (s, 0)) =
      CoefficientBassCompositeJ0PairedNull.newConePlus P p q s := by
  rw [(CoefficientBassPositiveC0CarrierSeed.source_contractions P
    p q s).2]
  change CoefficientBassPositiveC0CarrierSeed.plusCylinder P
    p q
      (nodePoint _ (sourceNullNode P _ _), s) =
    CoefficientBassPositiveC0CarrierSeed.plusCylinder P
      p q
        (CoefficientBassCompositeJ0Polynomial.movement P p q 1, s)
  rw [movement_terminal]

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0C0ContractionSeam
