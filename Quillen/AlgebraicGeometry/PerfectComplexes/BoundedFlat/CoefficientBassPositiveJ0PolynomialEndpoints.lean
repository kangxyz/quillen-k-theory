/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PolynomialMovement

/-! Full actual endpoint references connecting the polynomial movement to the chosen C0 rail. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0PolynomialEndpoints
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveJ0PolynomialMovement CoefficientBassPositiveC0PolynomialEndpoints
open CoefficientBassPositiveC0CarrierAttachment
open BassH0Merge (normalizedMap)
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The initial model is exactly the polynomial input of the original old cone. -/
theorem initial_model : (nodes P d 2).1 =
    normalizedMap (polynomialProjection P d) ≫
      normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map (arrow d))) := rfl

/-- The final dependent node retains the accepted direct-l coefficient transport in full. -/
theorem terminal_node : nodes P d 4 = actualSourceNullNode P d := by
  let ρ := (actualSourceNullNode P d).2
  let β := BinaryNormalizationSimplex.total
    (polynomialProjection P ((laurentUnderFunctor R).obj d)) (coefficientMap P (arrow d))
  let α := NativeSquareFiveSimplex.sourceIso
    (coefficientMap P ((polynomialUnderFunctor R).map (arrow d)))
    (polynomialProjection P d)
    (polynomialProjection P ((laurentUnderFunctor R).obj d)) (coefficientMap P (arrow d))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow d))
  change (⟨_, ((ρ ≪≫ β.symm) ≪≫ α.symm) ≪≫ (α ≪≫ β)⟩ : Node (reference P d)) =
    ⟨_, ρ⟩
  exact congrArg (fun η ↦ (⟨(actualSourceNullNode P d).1, η⟩ : Node (reference P d)))
    (show ((ρ ≪≫ β.symm) ≪≫ α.symm) ≪≫ (α ≪≫ β) = ρ by simp [Iso.trans_assoc])

/-- The complete terminal node is the accepted coefficient-polynomial source, before evaluation. -/
theorem terminal_coefficient_node : nodes P d 4 =
    coefficientPolynomialNodes P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) 0 :=
  (terminal_node P d).trans (actual_source_node P d).symm

/-- The attached terminal reference is the raw original positive rectangle's terminal node. -/
theorem attached_terminal_node :
    ordinaryAttachNode P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
      (nodes P d 4) =
    BassH0Merge.nodes P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
      (BassH0Diagram.plusFace.toOrderHom
        (DoubleSquareMergedSimplex.lastFace.toOrderHom (BassH0Merge.rightIndex 2))) := by
  rw [terminal_coefficient_node]
  exact (coefficient_column_nodes P ((polynomialUnderCoefficient R).app d)
    ((underToLaurent R).app d) 0).symm.trans
      (BassMOuterJoin.source_middle_plus_nodes P ((polynomialUnderCoefficient R).app d)
        ((underToLaurent R).app d) 2)

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0PolynomialEndpoints
