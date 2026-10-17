/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.Topology.DoubleMappingCylinder.Invariance

/-! The finite-source polynomial cap enters its actual ordinary chart cell with full anchors. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => input P p q w
local notation "F" => InputPolynomial.reference P p q w
local notation "Jd" => targetProjection P (d := d)
local notation "H" => BassProjectionPath.WholeReference.reference P d E
local notation "βd" => FourEdge.beta P d E
variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)

/-- Both the chart endpoint and the polynomial normalization remain in the Laurent anchor. -/
def laurentAnchor : (H).functor ≅ (F ≫ J).functor :=
  isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso P β hd) ≪≫
    (Functor.associator (E).functor (Jd).functor (J).functor).symm ≪≫
    isoWhiskerRight (polynomialAnchor P p q w) (J).functor

/-- Reanchor the full finite polynomial-cap reference in the original target-projected input
reference. -/
def polynomialPlacement : C(|parameterSSet F|, |parameterSSet (E ≫ Jd)|) :=
  mapParameter (CommonReferenceProduct.reanchor (polynomialAnchor P p q w))

/-- Reanchor the full chart-attached Laurent reference using the supplied target chart equation
`hd`. -/
def laurentPlacement : C(|parameterSSet (F ≫ J)|, |parameterSSet H|) :=
  mapParameter (CommonReferenceProduct.reanchor (laurentAnchor P p q w β hd))

/-- The full chart attachment square follows from the displayed Laurent anchor word. -/
theorem placement_node (N : Node F) :
    CommonReferenceProduct.reanchor (laurentAnchor P p q w β hd)
      (attachPostcompNode F J (F ≫ J) (Iso.refl _) N) =
    chartAttachmentNode P d E β hd
      (CommonReferenceProduct.reanchor (polynomialAnchor P p q w) N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [laurentAnchor, chartAttachmentNode, CommonReferenceProduct.postNode,
    CommonReferenceProduct.reanchor, attachPostcompNode, postcompNode,
    isoWhiskerRight_trans, Iso.refl_trans, Iso.trans_assoc]
  rfl

/-- The complete finite-source nerve meets the actual ordinary chart vertex. -/
theorem placement_parameter (y : |parameterSSet F|) :
    laurentPlacement P p q w β hd
      (SSet.toTop.map (attaching F J (F ≫ J) (Iso.refl _)) y) =
    SSet.toTop.map (FourEdge.chartMap P d E β hd) (polynomialPlacement P p q w y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  change mapParameter (CommonReferenceProduct.reanchor (laurentAnchor P p q w β hd))
      (mapParameter (attachPostcompNode F J (F ≫ J) (Iso.refl _))
        (CommonReferenceNerve.parameter F N z)) =
    mapParameter (chartAttachmentNode P d E β hd)
      (mapParameter (CommonReferenceProduct.reanchor (polynomialAnchor P p q w))
        (CommonReferenceNerve.parameter F N z))
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns ↦ CommonReferenceNerve.parameter H ns z)
    (funext (fun i ↦ placement_node P p q w β hd (N i)))

variable (v : parameterSSet (input P p q w ≫ targetProjection P (d := d)) ⟶
    FourEdgeTree.simplicial (input P p q w) (targetProjection P (d := d)))
  (hv : v ≫ FourEdge.beta P d (input P p q w) =
    FourEdge.chartMap P d (input P p q w) β hd)

/-- Place the polynomial cap at the supplied target-tree map `v`, retaining its prescribed chart
equation. -/
def placementVertex : |parameterSSet F| ⟶ FourEdgeTree.space E Jd :=
  TopCat.ofHom ((SSet.toTop.map v).hom.comp (polynomialPlacement P p q w))

include hv in
theorem placement_square :
    SSet.toTop.map (attaching F J (F ≫ J) (Iso.refl _)) ≫
      TopCat.ofHom (laurentPlacement P p q w β hd) =
    placementVertex P p q w v ≫ SSet.toTop.map βd := by
  ext y
  change laurentPlacement P p q w β hd (mapParameter
      (attachPostcompNode F J (F ≫ J) (Iso.refl _)) y) =
    SSet.toTop.map βd (SSet.toTop.map v (polynomialPlacement P p q w y))
  rw [← FourEdgeTree.realized_comp, hv]
  exact placement_parameter P p q w β hd y

theorem placement_erase :
    SSet.toTop.map (erase F) ≫ 𝟙 _ = placementVertex P p q w v ≫
      SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E Jd)) := by
  ext y
  exact Subsingleton.elim _ _

/-- The actual one-sheet quotient enters the chosen chart vertex and the same ordinary tip. -/
def place : C(carrier P p q w β, FourEdge.scalarCone P d E) :=
  (DoubleCylinder.map (first_isPushout F J (F ≫ J) (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (placementVertex P p q w v) (TopCat.ofHom (laurentPlacement P p q w β hd)) (𝟙 _)
    (placement_square P p q w β hd v hv) (placement_erase P p q w v)).hom

theorem place_laurent (y : |parameterSSet (F ≫ J)|) :
    place P p q w β hd v hv (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y) =
      FourEdgeTree.laurentInclusion E Jd H βd (laurentPlacement P p q w β hd y) := by
  have h₀ := congrArg (place P p q w β hd v hv)
    (FourEdgeTree.SetDescent.eval_realized_left
      (attaching F J (F ≫ J) (Iso.refl _)) (erase F) y)
  have h₁ := DoubleCylinder.map_left (first_isPushout F J (F ≫ J) (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (placementVertex P p q w v) (TopCat.ofHom (laurentPlacement P p q w β hd)) (𝟙 _)
    (placement_square P p q w β hd v hv) (placement_erase P p q w v) y
  exact h₀.trans (h₁.trans (FourEdgeTree.SetDescent.eval_realized_left
    βd (SSet.stdSimplex.isTerminalObj₀.from _) (laurentPlacement P p q w β hd y)).symm)

theorem place_cylinder (y : |parameterSSet F|) (h : I) :
    place P p q w β hd v hv (DoubleCylinder.realizedCylinder
      (attaching F J (F ≫ J) (Iso.refl _)) (erase F) (y, ULift.up h)) =
      FourEdgeTree.cylinder E Jd H βd (placementVertex P p q w v y, h) :=
  DoubleCylinder.map_cylinder_apply _ _ _ _ _ _ _ _ _

theorem place_tip :
    place P p q w β hd v hv
      (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) (default : |tipSSet.{u+1}|)) =
      FourEdgeTree.tip E Jd H βd := by
  have h₀ := congrArg (place P p q w β hd v hv)
    (FourEdgeTree.SetDescent.eval_realized_right
      (attaching F J (F ≫ J) (Iso.refl _)) (erase F) (default : |tipSSet.{u+1}|))
  have h₁ := DoubleCylinder.map_right (first_isPushout F J (F ≫ J) (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (placementVertex P p q w v) (TopCat.ofHom (laurentPlacement P p q w β hd)) (𝟙 _)
    (placement_square P p q w β hd v hv) (placement_erase P p q w v) default
  exact h₀.trans (h₁.trans (FourEdgeTree.SetDescent.eval_realized_right
    βd (SSet.stdSimplex.isTerminalObj₀.from _) default).symm)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
