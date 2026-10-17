/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcomp
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompAttachments

/-! The genuine polynomial triple sheet enters the ordinary triple reference
by source projection. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceProjection
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original normalized triple source reference for `p`, `q` and `w` before polynomial
extension. -/
abbrev input := NormalizedTripleSimplex.sourceMap
  (coefficientMap P w) (coefficientMap P q) (coefficientMap P p)
/-- The fixed polynomial triple reference carrying the original postcomposed cap. -/
abbrev polynomial := CoefficientBassRaw1PolynomialPostcomp.reference P p q w
/-- The normalized original polynomial projection at the source coefficient algebra `a`. -/
abbrev sourceProjection := normalizedMap (polynomialProjection P a)
/-- The normalized original polynomial projection at the target coefficient algebra `d`. -/
abbrev targetProjection := normalizedMap (polynomialProjection P d)
local notation "E" => input P p q w
local notation "F" => polynomial P p q w
local notation "A" => sourceProjection P (a := a)
local notation "Jd" => targetProjection P (d := d)
local notation "k" => coefficientMap P w ≫ coefficientMap P q ≫ coefficientMap P p
local notation "kp" =>
  CoefficientBassRaw1PolynomialPostcomp.lastArrow P w ≫
    CoefficientBassRaw1PolynomialPostcomp.secondArrow P q ≫
      CoefficientBassRaw1PolynomialPostcomp.firstArrow P p

/-- Naturality is taken at the literal composite; its polynomial source is not erased. -/
theorem projection_total : polynomialProjection P d ≫ k = kp ≫ polynomialProjection P a := by
  have h := (coefficientMap_naturality P (polynomialUnderCoefficient R) ((p ≫ q) ≫ w)).symm
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.id_obj, coefficientMap_comp, polynomialProjection, Category.assoc,
    CoefficientBassRaw1PolynomialPostcomp.firstArrow,
    CoefficientBassRaw1PolynomialPostcomp.secondArrow,
    CoefficientBassRaw1PolynomialPostcomp.lastArrow] using h

/-- Both binary normalization isomorphisms and the actual geometric naturality are retained. -/
def polynomialIso : (E ≫ Jd).functor ≅ (A ≫ F).functor :=
  (BinaryNormalizationSimplex.total (polynomialProjection P d) k).symm ≪≫
    eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) (projection_total P p q w)) ≪≫
    BinaryNormalizationSimplex.total kp (polynomialProjection P a)

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => F ≫ J
local notation "ε" => CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- The polynomial model and the full source-domain anchor survive before chart attachment. -/
def polynomialNode (N : CommonReferenceNerve.Node F) : CommonReferenceNerve.Node (E ≫ Jd) :=
  CommonReferenceProduct.reanchor (polynomialIso P p q w) (precompNode A N)

/-- The Laurent anchor includes the genuine chart endpoint and the precomposition associator. -/
def laurentIso : (BassProjectionPath.WholeReference.reference P d E).functor ≅ (A ≫ G).functor :=
  isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso P β hd) ≪≫
    CoefficientBassPolynomialSheetNormalization.laurentIso
      (A ≫ F) (E ≫ Jd) J (A ≫ G) ε (polynomialIso P p q w)

/-- Source projection acts on the full Laurent node before its exact target reference change. -/
def laurentNode (N : CommonReferenceNerve.Node G) :
    CommonReferenceNerve.Node (BassProjectionPath.WholeReference.reference P d E) :=
  CommonReferenceProduct.reanchor (laurentIso P p q w β hd) (precompNode A N)

/-- The entire polynomial attachment square commutes before any native evaluation. -/
theorem attachment_node (N : CommonReferenceNerve.Node F) :
    laurentNode P p q w β hd (attachPostcompNode F J G (Iso.refl _) N) =
      chartAttachmentNode P d E β hd (polynomialNode P p q w N) := by
  dsimp only [laurentNode]
  rw [CutOpenPrecomp.attachment_node]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [laurentIso, CoefficientBassPolynomialSheetNormalization.laurentIso,
    chartAttachmentNode, CommonReferenceProduct.postNode, CommonReferenceProduct.reanchor,
    attachPostcompNode, postcompNode, polynomialNode, isoWhiskerRight_trans,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  rfl

/-- The same full square holds on the complete realized polynomial reference nerve. -/
theorem attachment_parameter (y : |parameterSSet F|) :
    mapParameter (laurentNode P p q w β hd)
        (mapParameter (attachPostcompNode F J G (Iso.refl _)) y) =
      mapParameter (chartAttachmentNode P d E β hd)
        (mapParameter (polynomialNode P p q w) y) := by
  obtain ⟨n, ns, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ts ↦ parameter (BassProjectionPath.WholeReference.reference P d E) ts z)
    (funext (fun i ↦ attachment_node P p q w β hd (ns i)))

/-- The actual simplicial attachment retains both full node maps. -/
theorem attachment_simplicial :
    attaching F J G (Iso.refl _) ≫
        nerveMap (Codiscrete.functorOfFun (laurentNode P p q w β hd)) =
      nerveMap (Codiscrete.functorOfFun (polynomialNode P p q w)) ≫
        FourEdge.chartMap P d E β hd :=
  congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f))
    (funext (attachment_node P p q w β hd))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialSourceProjection
