/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityPositiveFactor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.UnitTrackPostcompSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-!
# The actual two-tip carrier for the original global input seed

The polynomial square and original Laurent total are the native reference maps. Their
ordinary attachment is the full polynomial-column anchor of the original positive rectangle.
The other attachment uses the original forward unit on that same Laurent reference. The
whole original polynomial movement attaches before native evaluation, including its four
ordered primitive edges and nonmonotone five-node word.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedCarrier
open CommonReferenceNerve BassH0Merge
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual polynomial square source, before either normalization track. -/
abbrev polyRef := NativeSquareFiveSimplex.source (polynomial.map g) (projection.app Y)

/-- The original normalized positive chart model map. -/
abbrev chart := BassH0Merge.normalizedMap (plus.app X)

/-- The actual outer Laurent total used by both original input rectangles. -/
abbrev laurentRef := InputDescSimplex.reference g

/-- The original five polynomial nodes include their complete equality-induced references. -/
abbrev polynomialNodes := NativeSquareFiveSimplex.nodes (polynomial.map g)
  (projection.app Y) (projection.app X) g (projection.naturality g)

/-- The full polynomial-column reference, retaining the actual chart-square and projection. -/
def ordinary : (laurentRef g).functor ≅ (polyRef g ≫ chart (X := X)).functor :=
  ProjectionRectangleSquareRows.polynomialAnchor (projection.app Y) (plus.app Y)
    (plus.app X) (polynomial.map g) (laurent.map g) (plus.naturality g)
    (laurentProjection.app Y) (plus_projection Y)

/-- The original forward unit on the actual old Laurent total. -/
def commonUnit : (laurentRef g).functor ≅ (laurentRef g).functor :=
  UnitTrackPostcompSimplex.sourceUnit (laurent.map g) (laurentProjection.app Y)
    (GlobalSchemeLaurentTrack.laurentScalar (op Y))

/-- The separate shifted attachment keeps the full original unit before the ordinary anchor. -/
def shifted : (laurentRef g).functor ≅ (polyRef g ≫ chart (X := X)).functor :=
  commonUnit g ≪≫ ordinary g

/-- The actual two-tip carrier; its polynomial tips are kept distinct. -/
abbrev Carrier := CutOpenCarrier.space (polyRef g) (chart (X := X)) (laurentRef g)
  (ordinary g) (shifted g)

/-- The entire original polynomial square moves in its own full-node nerve. -/
def movement : C(I, |nerve (Codiscrete (Node (polyRef g)))|) :=
  (parameter (polyRef g) (polynomialNodes g)).comp NativeSquareFiveSimplex.parameter.toContinuousMap

/-- Every original polynomial-square value is recovered at its own unchanged time. -/
theorem movement_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    pointwisePrespectrumFamily (polyRef g) n (movement g t) x =
      (polynomialSquareHomotopy g).level n (t, x) := by
  change pointwisePrespectrumFamily (polyRef g) n
    (parameter (polyRef g) (polynomialNodes g) (NativeSquareFiveSimplex.parameter t)) x = _
  rw [pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
  exact NativeSquareFiveSimplex.native (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g) n t x

/-- All five original polynomial-column nodes attach with their full reference isomorphisms. -/
theorem polynomial_nodes (i : Fin 5) :
    InputDescSimplex.nodes g (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i)) =
    attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g)
      (polynomialNodes g i) := by
  rw [InputDescSimplex.plus_nodes]
  exact ProjectionRectangleSquareRows.polynomial_row_nodes
    (projection.app Y) (plus.app Y) (projection.app X) (plus.app X) g
    (polynomial.map g) (laurent.map g) (projection.naturality g) (plus.naturality g)
    (laurentProjection.app Y) (plus_projection Y) i

/-- The four actually traversed primitive edges are ordered despite the full column word. -/
theorem polynomial_edges (i : Fin 4) : Monotone
    ((BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow) ∘
      (BassH1Support.edgeFace i).toOrderHom) :=
  BassH0Diagram.plusFace.toOrderHom.monotone.comp
    (ProjectionRectangleSquareRows.primitive_rows_monotone 1 i)

/-- The whole ordinary polynomial rail joins its cone attachment before native evaluation. -/
theorem movement_attach (t : I) :
    parameter (laurentRef g) (InputDescSimplex.nodes g)
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t) =
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g))
      (movement g t) := by
  rw [← ProjectionRectangleSquareRows.polynomial_parameter]
  change parameter (laurentRef g) (InputDescSimplex.nodes g)
    (StdSimplex.map (BassH0Diagram.plusFace.toOrderHom ∘
      ProjectionRectangleSquareRows.polynomialRow) (NativeSquareFiveSimplex.parameter t)) =
    mapParameter _ (parameter (polyRef g) (polynomialNodes g)
      (NativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact parameter_supported _ _ _
    (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow)
    (polynomial_nodes g) (BassH1Support.edgeFace i) (polynomial_edges i) z

/-- A complete shifted attached node retains the original common unit and ordinary anchor. -/
theorem shifted_node (N : Node (polyRef g)) :
    anchorNode (commonUnit g)
      (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) N) =
    attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (shifted g) N := by
  apply congrArg (fun a ↦ (⟨N.1 ≫ chart (X := X), a⟩ : Node (laurentRef g)))
  exact (Iso.trans_assoc _ _ _).symm

/-- The whole shifted polynomial rail uses the same movement with its separate attachment. -/
theorem shifted_movement_attach (t : I) :
    mapParameter (anchorNode (commonUnit g))
      (parameter (laurentRef g) (InputDescSimplex.nodes g)
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t)) =
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (shifted g))
      (movement g t) := by
  rw [movement_attach]
  exact reanchor_attach_parameter (polyRef g) (chart (X := X)) (laurentRef g)
    (commonUnit g) (ordinary g) (movement g t)

/-- The two actual tips remain different even though both evaluate to the native cone point. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) (shifted g) ≠
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) (shifted g) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedCarrier
