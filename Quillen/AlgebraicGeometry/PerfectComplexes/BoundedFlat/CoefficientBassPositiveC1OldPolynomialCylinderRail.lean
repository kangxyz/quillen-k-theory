/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1PolynomialSourceReference
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PairedNull

/-! The full polynomial source reference determines both entire old cylinder rails. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Simplicial
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1OldPolynomialCylinderRail
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


variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Exact polynomial source point, with the original direct-l square reference. -/
theorem polynomial_zero :
    polynomialParameter P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) 0 =
        CoefficientBassPositiveJ0PolynomialMovement.movement P d 0 := by
  change parameter _ _ (pausedBinaryParameter 0) =
    parameter _ _ (NativeSquareFiveSimplex.parameter 0)
  rw [Path.source, Path.source, parameter_vertex, parameter_vertex,
    CoefficientBassPositiveC1PolynomialSourceReference.polynomial_source_node]

/-- Every ordinary cylinder coordinate uses that full source point and the original minus tip. -/
theorem minus_cylinder (s : I) :
    CoefficientBassPositiveC0CarrierSeed.minusCylinder P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
      (polynomialParameter P ((polynomialUnderCoefficient R).app d)
        ((underToLaurent R).app d) 0, s) =
      CoefficientBassPositiveJ0PairedNull.oldConeMinus P d s := by
  rw [polynomial_zero]; rfl

/-- Every shifted cylinder coordinate retains the separate plus attachment and plus tip. -/
theorem plus_cylinder (s : I) :
    CoefficientBassPositiveC0CarrierSeed.plusCylinder P
      ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
      (polynomialParameter P ((polynomialUnderCoefficient R).app d)
        ((underToLaurent R).app d) 0, s) =
      CoefficientBassPositiveJ0PairedNull.oldConePlus P d s := by
  rw [polynomial_zero]; rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveC1OldPolynomialCylinderRail
