/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeGeometricCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1PolynomialSourceReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldPositiveSourceRails
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldUnitSourceRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldChartClockedRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace

/-! Full source rails depend only on the composite coefficient arrow. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v w
namespace Quillen.PerfectComplexes.CoefficientBassNegativeSeedReferenceRails
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierRails CoefficientBassPositiveC0PolynomialEndpoints
open CoefficientBassPositiveC0CarrierSeed

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

private theorem dependent_congr {A : Sort v} {B : A → Sort w}
    (f : (a : A) → B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

open CoefficientBassNegativeCarrierReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a c : Under R}

/-- Source data adds only the composite arrow and its exact geometric proof fields. -/
structure SeedGeometry where
  /-- The polynomial and coefficient totals, with their chart compatibility. -/
  carrier : Geometry P (a := a) (c := c)
  /-- The composite coefficient arrow from `a` to `c`. -/
  arrow : a ⟶ c
  h0Reference : (Geometry.laurentRef P carrier).functor =
    (BassH0Diagram.reference P arrow).functor
  polynomialSquare : polynomialProjection P c ≫ carrier.coefficient =
    carrier.polynomial ≫ polynomialProjection P a
  coefficientEq : carrier.coefficient = coefficientMap P arrow

namespace SeedGeometry
variable (D : SeedGeometry P (a := a) (c := c))

/-- The inclusion of the Laurent reference space into the geometric two-tip carrier. -/
abbrev includeLaurent := CutOpenCarrier.laurentInclusion
  (Geometry.polyRef P D.carrier) (chartMap P (c := c)) (Geometry.laurentRef P D.carrier)
  (Geometry.ordinary P D.carrier) (Geometry.shifted P D.carrier)
/-- The ordinary polynomial cylinder, with cylinder time in the second coordinate. -/
abbrev minusCylinder := CutOpenCarrier.cylinderMinus
  (Geometry.polyRef P D.carrier) (chartMap P (c := c)) (Geometry.laurentRef P D.carrier)
  (Geometry.ordinary P D.carrier) (Geometry.shifted P D.carrier)
/-- The shifted polynomial cylinder, with cylinder time in the second coordinate. -/
abbrev plusCylinder := CutOpenCarrier.cylinderPlus
  (Geometry.polyRef P D.carrier) (chartMap P (c := c)) (Geometry.laurentRef P D.carrier)
  (Geometry.ordinary P D.carrier) (Geometry.shifted P D.carrier)

/-- The H0 diagram nodes reanchored to the geometric Laurent reference. -/
def h0Nodes := ModelSimplex.reanchorNodes
  (F₀ := Geometry.laurentRef P D.carrier) (F₁ := BassH0Diagram.reference P D.arrow)
  (eqToIso D.h0Reference) (BassH0Diagram.nodes P D.arrow)

/-- A Laurent parameter in the carrier, with forward unit reanchoring when `e` is `true`. -/
def laurentPoint (e : Bool)
    (z : |nerve (Codiscrete (Node (Geometry.laurentRef P D.carrier)))|) :=
  includeLaurent P D (if e then mapParameter
    (BassH0Merge.anchorNode (Geometry.unit P D.carrier)) z else z)

/-- The three-node H0 projection path at its original binary time `s`. -/
def projectionParameter (s : I) :=
  parameter (Geometry.laurentRef P D.carrier)
    (fun i : Fin 3 ↦ h0Nodes P D (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (BassH0Merge.rightIndex i))))
    (binaryPath (k := 2) 0 1 2 s)

/-- The H0 projection path in the ordinary (`false`) or shifted (`true`) sheet. -/
def projection (e : Bool) (s : I) := laurentPoint P D e (projectionParameter P D s)

/-- A point of the H0 characteristic simplex in the ordinary (`false`) or shifted (`true`)
sheet. -/
def h0Point (e : Bool) (t : StdSimplex ℝ (Fin 31)) :=
  laurentPoint P D e (parameter (Geometry.laurentRef P D.carrier) (h0Nodes P D) t)

/-- The ten-node forward-unit characteristic map reanchored to the geometric Laurent reference. -/
def unitPoint (t : StdSimplex ℝ (Fin 10)) := includeLaurent P D
  (mapParameter (BassH0Merge.anchorNode (eqToIso D.h0Reference))
    (parameter (CoefficientLaurentUnitTenNodes.source P D.arrow)
      (CoefficientLaurentUnitTenNodes.nodes P D.arrow) t))

/-- This is the entire source-null reference, including both original binary totals. -/
def polynomialNode : Node (Geometry.polyRef P D.carrier) :=
  ⟨polynomialNullInput P D.arrow,
    ((NativeSquareFiveSimplex.sourceIso (polynomialProjection P c) D.carrier.coefficient
      D.carrier.polynomial (polynomialProjection P a) D.polynomialSquare ≪≫
        BinaryNormalizationSimplex.total D.carrier.polynomial
          (polynomialProjection P a)).symm ≪≫
      BinaryNormalizationSimplex.total (polynomialProjection P c) D.carrier.coefficient) ≪≫
      eqToIso (congrArg (fun f ↦
        (BassH0Merge.normalizedMap f ≫
          BassH0Merge.normalizedMap (polynomialProjection P c)).functor) D.coefficientEq)⟩

/-- The C0 source-null polynomial node at cylinder time `s`, using the tip selected by `e`. -/
def c0Cylinder (e : Bool) (s : I) :=
  if e then plusCylinder P D (nodePoint _ (polynomialNode P D), s)
  else minusCylinder P D (nodePoint _ (polynomialNode P D), s)

/-- The polynomial reference node at cylinder time `s`, using the tip selected by `e`. -/
def c1Cylinder (e : Bool) (s : I) :=
  if e then plusCylinder P D
    (nodePoint (Geometry.polyRef P D.carrier) ⟨Geometry.polyRef P D.carrier, Iso.refl _⟩, s)
  else minusCylinder P D
    (nodePoint (Geometry.polyRef P D.carrier) ⟨Geometry.polyRef P D.carrier, Iso.refl _⟩, s)

end SeedGeometry

variable {b b' : Under R} (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The source datum uses exactly the original full reference and geometric proofs. -/
def seedGeometry : SeedGeometry P (a := a) (c := c) where
  carrier := geometry P p q
  arrow := p ≫ q
  h0Reference := BassH0Merge.reference_eq P p q
  polynomialSquare := CoefficientBassPositiveC1PolynomialSourceReference.outer_square P p q
  coefficientEq := (coefficientMap_comp P p q).symm

/-- Proof irrelevance preserves all references while the two geometric totals remain equal. -/
theorem seed_geometry_eq (h : p ≫ q = p' ≫ q') : seedGeometry P p q = seedGeometry P p' q' := by
  have aux {D E : SeedGeometry P (a := a) (c := c)}
      (hD : D.carrier = E.carrier) (hw : D.arrow = E.arrow) : D = E := by
    cases D
    cases E
    cases hD
    cases hw
    rfl
  exact aux (D := seedGeometry P p q) (E := seedGeometry P p' q')
    (geometry_eq P p q p' q' h) h

/-- The entire original C0 source-null node has this composite-only normal form. -/
theorem c0_source_node_normal : sourceNullNode P p q =
    SeedGeometry.polynomialNode P (seedGeometry P p q) := by
  dsimp only [sourceNullNode, sourceNullAnchor, polynomialCoefficientAnchor,
    SeedGeometry.polynomialNode, seedGeometry, geometry]
  rw [CoefficientBassPositiveC1PolynomialSourceReference.moving_side_reference]
  rfl

/-- The complete C1 initial polynomial vertex is the reference node itself. -/
theorem c1_polynomial_source : polynomialParameter P p q 0 =
    nodePoint (polynomialReference P p q)
      (⟨polynomialReference P p q, Iso.refl _⟩ : Node (polynomialReference P p q)) := by
  change parameter _ _ (pausedBinaryParameter 0) = _
  rw [Path.source, parameter_vertex]
  have hn : polynomialNodes P p q 0 =
      (⟨polynomialReference P p q, Iso.refl _⟩ : Node (polynomialReference P p q)) := by
    change (⟨polynomialReference P p q,
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor (Iso.refl _)⟩ :
      Node (polynomialReference P p q)) = _
    rw [isoWhiskerLeft_refl]
    rfl
  rw [hn]

/-- The whole minus C0 projection rail preserves its complete composite reference. -/
theorem c0_projection_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (projectionMinus P p q (s, 0)) (projectionMinus P p' q' (s, 0)) := by
  rw [source_projection, source_projection]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.projection P D false s)
    (seed_geometry_eq P p q p' q' h)

/-- The whole plus C0 projection rail preserves its complete composite reference. -/
theorem c0_projection_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (projectionPlus P p q (s, 0)) (projectionPlus P p' q' (s, 0)) := by
  rw [source_projection_shifted, source_projection_shifted]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.projection P D true s)
    (seed_geometry_eq P p q p' q' h)

/-- The minus C0 cylinder retains its full source-null anchor and its own tip. -/
theorem c0_contraction_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (contractionMinus P p q (s, 0)) (contractionMinus P p' q' (s, 0)) := by
  rw [(source_contractions P p q s).1, (source_contractions P p' q' s).1,
    c0_source_node_normal, c0_source_node_normal]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.c0Cylinder P D false s)
    (seed_geometry_eq P p q p' q' h)

/-- The plus C0 cylinder retains its full source-null anchor and its own tip. -/
theorem c0_contraction_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (contractionPlus P p q (s, 0)) (contractionPlus P p' q' (s, 0)) := by
  rw [(source_contractions P p q s).2, (source_contractions P p' q' s).2,
    c0_source_node_normal, c0_source_node_normal]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.c0Cylinder P D true s)
    (seed_geometry_eq P p q p' q' h)

/-- The source unit keeps the direct-composite W edge and its unchanged scalar clock. -/
theorem c0_unit_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (forwardUnit P p q (s, 0)) (forwardUnit P p' q' (s, 0)) := by
  rw [source_unit, source_unit]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.unitPoint P D (CoefficientLaurentUnitTenNodes.W s))
    (seed_geometry_eq P p q p' q' h)

/-- The minus C1 old-positive rail is the full anchored direct-composite D edge. -/
theorem c1_positive_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.positiveMinus P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.positiveMinus P p' q' (s, 0)) := by
  change HEq (includeLaurent P p q
    (CoefficientBassPositiveC1SourceProductStrips.positiveParameter P p q (0, s)))
    (includeLaurent P p' q'
      (CoefficientBassPositiveC1SourceProductStrips.positiveParameter P p' q' (0, s)))
  rw [CoefficientBassPositiveC1OldPositiveSourceRails.source_parameter,
    CoefficientBassPositiveC1OldPositiveSourceRails.source_parameter]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.h0Point P D false
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace s))
    (seed_geometry_eq P p q p' q' h)

/-- The plus C1 old-positive rail is the full anchored direct-composite D edge. -/
theorem c1_positive_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.positivePlus P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.positivePlus P p' q' (s, 0)) := by
  change HEq (includeLaurent P p q
    (mapParameter (CommonReferenceProduct.reanchor
      (LaurentUnitReferenceSpecialization.commonUnit P p q))
      (CoefficientBassPositiveC1SourceProductStrips.positiveParameter P p q (0, s))))
    (includeLaurent P p' q'
      (mapParameter (CommonReferenceProduct.reanchor
        (LaurentUnitReferenceSpecialization.commonUnit P p' q'))
        (CoefficientBassPositiveC1SourceProductStrips.positiveParameter P p' q' (0, s))))
  rw [CoefficientBassPositiveC1OldPositiveSourceRails.source_parameter,
    CoefficientBassPositiveC1OldPositiveSourceRails.source_parameter]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.h0Point P D true
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace s))
    (seed_geometry_eq P p q p' q' h)

/-- The C1 source unit retains the whole original direct-composite V edge. -/
theorem c1_unit_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1SeedFace.forwardUnit P p q (s, 0))
      (CoefficientBassPositiveC1SeedFace.forwardUnit P p' q' (s, 0)) := by
  change HEq (includeLaurent P p q
    (CoefficientBassPositiveC1SourceProductStrips.unitParameter P p q (0, s)))
    (includeLaurent P p' q'
      (CoefficientBassPositiveC1SourceProductStrips.unitParameter P p' q' (0, s)))
  rw [CoefficientBassPositiveC1OldUnitSourceRail.source_parameter,
    CoefficientBassPositiveC1OldUnitSourceRail.source_parameter]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.unitPoint P D (CoefficientLaurentUnitTenNodes.V s))
    (seed_geometry_eq P p q p' q' h)

/-- The minus C1 chart source retains both original half clocks. -/
theorem c1_chart_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1InitialMovingNull.firstSwap P p q (s, 0))
      (CoefficientBassPositiveC1InitialMovingNull.firstSwap P p' q' (s, 0)) := by
  change HEq (includeLaurent P p q (chartParameter P p q (0, s)))
    (includeLaurent P p' q' (chartParameter P p' q' (0, s)))
  rw [CoefficientBassPositiveC1OldChartClockedRail.chart_zero,
    CoefficientBassPositiveC1OldChartClockedRail.chart_zero]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.h0Point P D false
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace s))
    (seed_geometry_eq P p q p' q' h)

/-- The minus C1 old cylinder starts at the complete reference node. -/
theorem c1_cylinder_minus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1InitialMovingNull.lastSwap P p q (s, 0))
      (CoefficientBassPositiveC1InitialMovingNull.lastSwap P p' q' (s, 0)) := by
  change HEq (minusCylinder P p q (polynomialParameter P p q 0, s))
    (minusCylinder P p' q' (polynomialParameter P p' q' 0, s))
  rw [c1_polynomial_source, c1_polynomial_source]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.c1Cylinder P D false s)
    (seed_geometry_eq P p q p' q' h)

/-- The plus C1 chart source retains both original half clocks. -/
theorem c1_chart_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1ShiftedInitialMovingNull.firstSwap P p q (s, 0))
      (CoefficientBassPositiveC1ShiftedInitialMovingNull.firstSwap P p' q' (s, 0)) := by
  change HEq (includeLaurent P p q
    (mapParameter (CommonReferenceProduct.reanchor
      (LaurentUnitReferenceSpecialization.commonUnit P p q)) (chartParameter P p q (0, s))))
    (includeLaurent P p' q'
      (mapParameter (CommonReferenceProduct.reanchor
        (LaurentUnitReferenceSpecialization.commonUnit P p' q'))
        (chartParameter P p' q' (0, s))))
  rw [CoefficientBassPositiveC1OldChartClockedRail.chart_zero,
    CoefficientBassPositiveC1OldChartClockedRail.chart_zero]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.h0Point P D true
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace s))
    (seed_geometry_eq P p q p' q' h)

/-- The plus C1 old cylinder starts at the complete reference node. -/
theorem c1_cylinder_plus_heq (h : p ≫ q = p' ≫ q') (s : I) :
    HEq (CoefficientBassPositiveC1ShiftedInitialMovingNull.lastSwap P p q (s, 0))
      (CoefficientBassPositiveC1ShiftedInitialMovingNull.lastSwap P p' q' (s, 0)) := by
  change HEq (plusCylinder P p q (polynomialParameter P p q 0, s))
    (plusCylinder P p' q' (polynomialParameter P p' q' 0, s))
  rw [c1_polynomial_source, c1_polynomial_source]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦
      SeedGeometry.c1Cylinder P D true s)
    (seed_geometry_eq P p q p' q' h)

end Quillen.PerfectComplexes.CoefficientBassNegativeSeedReferenceRails
