/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Polynomial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PolynomialAttachment

/-! Full ordinary attachment for the original composite-arrow polynomial movement. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0Attachment
open CommonReferenceNerve BassH0Merge BassH1Join
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierAttachment
open CoefficientBassCompositeJ0Polynomial
open CoefficientBassPositiveJ0PolynomialAttachment (squareSource raw_row_form commonAnchor)
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The attached row uses the original ordinary anchor and the complete polynomial reference. -/
def attachedAnchor : (laurentReference P p q).functor ≅
    (squareSource P (p ≫ q) ≫ chartMap P (c := c)).functor :=
  ordinaryAnchor P p q ≪≫ isoWhiskerRight
    (CoefficientBassCompositeJ0Polynomial.sourceAnchor P p q) (chartMap P (c := c)).functor

/-- Attachment commutes with the whole polynomial reference change, not only its vertices. -/
theorem attached_row_form (i : Fin 5) :
    ordinaryAttachNode P p q ((CoefficientBassCompositeJ0Polynomial.nodes P p q) i) =
        postReferenceNode (laurentReference P p q) (chartMap P (c := c)) (attachedAnchor P p q)
        ((originalNodes P p q) i) :=
  post_anchor_node (laurentReference P p q) (chartMap P (c := c)) (ordinaryAnchor P p q)
    (CoefficientBassCompositeJ0Polynomial.sourceAnchor P p q) ((originalNodes P p q) i)

/-- One proved full terminal reference identifies all five original attached nodes. -/
theorem full_nodes (i : Fin 5) :
    BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) = ordinaryAttachNode P p q
          ((CoefficientBassCompositeJ0Polynomial.nodes P p q) i) := by
  apply post_families_match (laurentReference P p q) (chartMap P (c := c))
    (squareSource P (p ≫ q)) (originalNodes P p q)
    (raw_row_form P p q) (attached_row_form P p q) 4 ?_ i
  exact (CoefficientBassCompositeJ0Polynomial.attached_terminal_node P p q).symm

/-- Only the four primitive edges are ordered; the complete polynomial row is nonmonotone. -/
theorem primitive_edges (i : Fin 4) : Monotone
    ((BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow) ∘
      (BassH1Support.edgeFace i).toOrderHom) :=
  BassH0Diagram.plusFace.toOrderHom.monotone.comp
    (ProjectionRectangleSquareRows.primitive_rows_monotone 1 i)

/-- The full original Ppath attaches at its unchanged reversed-first, forward-second clock. -/
theorem movement_attach (t : I) :
    parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t) =
    mapParameter (ordinaryAttachNode P p q)
      (CoefficientBassCompositeJ0Polynomial.movement P p q t) := by
  rw [← ProjectionRectangleSquareRows.polynomial_parameter]
  change parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (StdSimplex.map
        (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow)
        (NativeSquareFiveSimplex.parameter t)) =
    mapParameter (ordinaryAttachNode P p q)
      (parameter (reference P p q) (CoefficientBassCompositeJ0Polynomial.nodes P p q)
          (NativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact parameter_supported (laurentReference P p q) (fun j ↦ ordinaryAttachNode P p q
      ((CoefficientBassCompositeJ0Polynomial.nodes P p q) j))
    (BassH0Merge.nodes P p q)
    (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow)
    (full_nodes P p q) (BassH1Support.edgeFace i) (primitive_edges i) z

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0Attachment
