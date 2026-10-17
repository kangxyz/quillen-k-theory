/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPolynomialNodes

/-!
# Exact finite polynomial parameters for the left route

The two continuous paths keep the original five-node square clock. Their attachments and
three endpoint identities hold in the actual common-reference nerves, before evaluation.
No nonmonotone five-node word is declared to be an ordered simplex face.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftPolynomialParameters
open BassH0Merge BassH1Join CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierAttachment
open CoefficientBassPositiveC0PolynomialEndpoints CoefficientBassPositiveLeftPolynomialNodes

private theorem parameter_vertex {V W : Model.{v}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → Node F) (i : Fin (k + 1)) :
    parameter F N (StdSimplex.single i) = nodePoint F (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) = StdSimplex.single i := by
    rw [StdSimplex.map_single]
    rfl
  rw [← hm, parameter_face]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The p polynomial square postcomposed by q, with its original two-binary clock. -/
def firstParameter : C(I, |nerve (Codiscrete (Node (polynomialReference P p q)))|) :=
  (parameter (polynomialReference P p q) (firstNodes P p q)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

/-- The q polynomial square precomposed by p, with the same original square clock. -/
def secondParameter : C(I, |nerve (Codiscrete (Node (polynomialReference P p q)))|) :=
  (parameter (polynomialReference P p q) (secondNodes P p q)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

/-- The first complete family attaches to the original product-column characteristic map. -/
theorem first_attach_parameter (t : I) :
    mapParameter (ordinaryAttachNode P p q) (firstParameter P p q t) =
      parameter (laurentReference P p q)
        (fun i ↦ BassH1References.chartNodes P p q (underToLaurent R)
          (laurentPlus_projection P b) (Quillen.SimplexGrid.index 4 4 (i, 4)))
        (NativeSquareFiveSimplex.parameter t) := by
  change mapParameter _ (parameter _ _ _) = _
  rw [mapParameter_parameter]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter t))
    (funext (first_attach_nodes P p q))

/-- The second complete family attaches to the original middle-row characteristic map. -/
theorem second_attach_parameter (t : I) :
    mapParameter (ordinaryAttachNode P p q) (secondParameter P p q t) =
      parameter (laurentReference P p q)
        (fun i ↦ BassH1References.middleNodes P p q
          (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)))
        (NativeSquareFiveSimplex.parameter t) := by
  change mapParameter _ (parameter _ _ _) = _
  rw [mapParameter_parameter]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter t))
    (funext (second_attach_middle_nodes P p q))

/-- The entire first shifted parameter has the actual shifted product-column references. -/
theorem first_shifted_attach_parameter (t : I) :
    mapParameter (shiftedAttachNode P p q) (firstParameter P p q t) =
      parameter (laurentReference P p q)
        (fun i ↦ anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
          (BassH1References.chartNodes P p q (underToLaurent R)
            (laurentPlus_projection P b) (Quillen.SimplexGrid.index 4 4 (i, 4))))
        (NativeSquareFiveSimplex.parameter t) := by
  change mapParameter _ (parameter _ _ _) = _
  rw [mapParameter_parameter]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter t))
    (funext (first_shifted_attach_nodes P p q))

/-- The entire second shifted parameter has the actual shifted middle-row references. -/
theorem second_shifted_attach_parameter (t : I) :
    mapParameter (shiftedAttachNode P p q) (secondParameter P p q t) =
      parameter (laurentReference P p q)
        (fun i ↦ anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
          (BassH1References.middleNodes P p q
            (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i))))
        (NativeSquareFiveSimplex.parameter t) := by
  change mapParameter _ (parameter _ _ _) = _
  rw [mapParameter_parameter]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter t))
    (funext (second_shifted_attach_nodes P p q))

/-- The first source is the characteristic vertex of the exact C1 terminal polynomial node. -/
theorem first_source_parameter : firstParameter P p q 0 =
    nodePoint (polynomialReference P p q) (polynomialNodes P p q 2) := by
  change parameter _ _ (NativeSquareFiveSimplex.parameter 0) = _
  rw [Path.source, parameter_vertex, first_source_node]

/-- The two finite paths share the same whole polynomial-nerve endpoint M13. -/
theorem first_target_second_source_parameter :
    firstParameter P p q 1 = secondParameter P p q 0 := by
  change parameter _ _ (NativeSquareFiveSimplex.parameter 1) =
    parameter _ _ (NativeSquareFiveSimplex.parameter 0)
  rw [Path.target, Path.source, parameter_vertex, parameter_vertex, first_target_second_source]

/-- The second target is the characteristic vertex of the original q-pre-p null input. -/
theorem second_target_parameter : secondParameter P p q 1 =
    nodePoint (polynomialReference P p q) (targetNullNode P p q) := by
  change parameter _ _ (NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target, parameter_vertex, second_target_node]

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftPolynomialParameters
