/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PolynomialEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows

/-! Full reference cancellation and four-edge attachment of the original polynomial movement. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0PolynomialAttachment
open CommonReferenceNerve BassH0Merge BassH1Join
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The unchanged original polynomial square source for an arbitrary coefficient arrow. -/
abbrev squareSource {a b : Under R} (w : a ⟶ b) := NativeSquareFiveSimplex.source
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)

/-- Both original normalization intermediates and the geometric square equality are retained. -/
abbrev squareNodes {a b : Under R} (w : a ⟶ b) := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((polynomialUnderFunctor R).map w)) (polynomialProjection P a)
  (polynomialProjection P b) (coefficientMap P w)
  (coefficientMap_naturality P (polynomialUnderCoefficient R) w)

/-- The original raw positive rectangle's entire polynomial-column reference. -/
def rawAnchor {a b : Under R} (w : a ⟶ b) :
    (BassH0Diagram.reference P w).functor ≅
      (squareSource P w ≫ chartMap P (c := b)).functor :=
  ProjectionRectangleSquareRows.polynomialAnchor
    (polynomialProjection P a) (laurentPlus P a) (laurentPlus P b)
    (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap_naturality P (underToLaurent R) w)
    (laurentProjection P a) (laurentPlus_projection P a)

/-- The common Laurent reference keeps its exact geometric-total equality transport. -/
def commonAnchor {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c) :
    (laurentReference P p q).functor ≅
      (squareSource P (p ≫ q) ≫ chartMap P (c := c)).functor :=
  eqToIso (BassH0Merge.reference_eq P p q) ≪≫ rawAnchor P (p ≫ q)

/-- All five raw nodes are the postcomposed original square in the common reference. -/
theorem raw_row_form {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c) (i : Fin 5) :
    BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) =
    postReferenceNode (laurentReference P p q) (chartMap P (c := c))
      (commonAnchor P p q) (squareNodes P (p ≫ q) i) := by
  change anchorNode (eqToIso (BassH0Merge.reference_eq P p q))
    (BassH0Diagram.nodes P (p ≫ q) (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i))) = _
  rw [BassH0Diagram.plus_nodes]
  dsimp only [BassH0Diagram.plusNodes, BassH0Diagram.chartNodes]
  rw [ProjectionRectangleSquareRows.polynomial_row_nodes]
  exact anchor_post_node _ _ _ _

/-- Equality of actual arrows transports the whole postcomposed family, including references. -/
theorem transport_row {a b : Under R} (w w' : a ⟶ b) (h : w = w')
    (F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj b))))
    (ρ : F.functor ≅ (squareSource P w ≫ chartMap P (c := b)).functor) (i : Fin 5) :
    postReferenceNode F (chartMap P (c := b)) ρ (squareNodes P w i) =
    postReferenceNode F (chartMap P (c := b))
      (ρ ≪≫ eqToIso (congrArg
        (fun v ↦ (squareSource P v ≫ chartMap P (c := b)).functor) h))
      (squareNodes P w' i) := by
  subst w'
  simp only [eqToIso_refl, Iso.trans_refl]

variable (d : Under R)
/-- The actual first coefficient arrow, without notation quotation. -/
abbrev chosenP := (polynomialUnderCoefficient R).app d
/-- The actual positive Laurent chart arrow, without notation quotation. -/
abbrev chosenQ := (underToLaurent R).app d
/-- The original direct Laurent coefficient arrow. -/
abbrev chosenW := CoefficientBassPositiveJ0PolynomialMovement.arrow d
/-- The unchanged chosen polynomial reference. -/
abbrev chosenF := CoefficientBassPositiveJ0PolynomialMovement.reference P d
/-- The unchanged common Laurent reference. -/
abbrev chosenG := laurentReference P (chosenP d) (chosenQ d)
/-- The original target positive chart model map. -/
abbrev chosenJ := chartMap P (c := (laurentUnderFunctor R).obj d)
/-- All five original polynomial nodes in the chosen reference. -/
abbrev chosenN := CoefficientBassPositiveJ0PolynomialMovement.nodes P d
/-- All five native polynomial-square nodes before reference change. -/
abbrev chosenD := CoefficientBassPositiveJ0PolynomialMovement.originalNodes P d

/-- The actual p;q=l equation remains explicit in the raw-row anchor. -/
def actualRawAnchor : (chosenG P d).functor ≅ (squareSource P (chosenW d) ≫ (chosenJ P d)).functor
      :=
  commonAnchor P (chosenP d) (chosenQ d) ≪≫ eqToIso (congrArg
    (fun v ↦ (squareSource P v ≫ (chosenJ P d)).functor) (polynomialUnderCoefficient_toLaurent R d))

/-- The attached row uses the original ordinary anchor and the complete polynomial reference. -/
def attachedAnchor : (chosenG P d).functor ≅ (squareSource P (chosenW d) ≫ (chosenJ P d)).functor :=
  ordinaryAnchor P (chosenP d) (chosenQ d) ≪≫ isoWhiskerRight
    (CoefficientBassPositiveJ0PolynomialMovement.sourceAnchor P d) (chosenJ P d).functor

/-- Every actual raw reference retains the p;q=l transport before reference cancellation. -/
theorem actual_raw_row_form (i : Fin 5) :
    BassH0Merge.nodes P (chosenP d) (chosenQ d) (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) =
    postReferenceNode (chosenG P d) (chosenJ P d) (actualRawAnchor P d) ((chosenD P d) i) :=
  (raw_row_form P (chosenP d) (chosenQ d) i).trans
    (transport_row P ((chosenP d) ≫ (chosenQ d)) (chosenW d) (polynomialUnderCoefficient_toLaurent
      R d)
      (chosenG P d) (commonAnchor P (chosenP d) (chosenQ d)) i)

/-- Attachment commutes with the whole polynomial reference change, not only its vertices. -/
theorem attached_row_form (i : Fin 5) :
    ordinaryAttachNode P (chosenP d) (chosenQ d) ((chosenN P d) i) = postReferenceNode (chosenG P
      d) (chosenJ P d) (attachedAnchor P d) ((chosenD P d) i) :=
  post_anchor_node (chosenG P d) (chosenJ P d) (ordinaryAnchor P (chosenP d) (chosenQ d))
    (CoefficientBassPositiveJ0PolynomialMovement.sourceAnchor P d) ((chosenD P d) i)

/-- One proved full terminal reference identifies all five original attached nodes. -/
theorem full_nodes (i : Fin 5) :
    BassH0Merge.nodes P (chosenP d) (chosenQ d) (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) = ordinaryAttachNode P (chosenP d) (chosenQ
      d) ((chosenN P d) i) := by
  apply post_families_match (chosenG P d) (chosenJ P d) (squareSource P (chosenW d)) (chosenD P d)
    (actual_raw_row_form P d) (attached_row_form P d) 4 ?_ i
  exact (CoefficientBassPositiveJ0PolynomialEndpoints.attached_terminal_node P d).symm

/-- Only the four primitive edges are ordered; the complete polynomial row is nonmonotone. -/
theorem primitive_edges (i : Fin 4) : Monotone
    ((BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow) ∘
      (BassH1Support.edgeFace i).toOrderHom) :=
  BassH0Diagram.plusFace.toOrderHom.monotone.comp
    (ProjectionRectangleSquareRows.primitive_rows_monotone 1 i)

/-- The full original Ppath attaches at its unchanged reversed-first, forward-second clock. -/
theorem movement_attach (t : I) :
    parameter (chosenG P d) (BassH0Merge.nodes P (chosenP d) (chosenQ d))
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t) =
    mapParameter (ordinaryAttachNode P (chosenP d) (chosenQ d))
      (CoefficientBassPositiveJ0PolynomialMovement.movement P d t) := by
  rw [← ProjectionRectangleSquareRows.polynomial_parameter]
  change parameter (chosenG P d) (BassH0Merge.nodes P (chosenP d) (chosenQ d))
      (StdSimplex.map
        (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow)
        (NativeSquareFiveSimplex.parameter t)) =
    mapParameter (ordinaryAttachNode P (chosenP d) (chosenQ d))
      (parameter (chosenF P d) (chosenN P d) (NativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact parameter_supported (chosenG P d) (fun j ↦ ordinaryAttachNode P (chosenP d) (chosenQ d)
      ((chosenN P d) j))
    (BassH0Merge.nodes P (chosenP d) (chosenQ d))
    (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow)
    (full_nodes P d) (BassH1Support.edgeFace i) (primitive_edges i) z

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0PolynomialAttachment
