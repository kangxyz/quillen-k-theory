/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed

/-! The complete carrier reference depends on the composite coefficient arrow. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.IteratedS
open scoped Topology
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassNegativeCarrierReference
open CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a c : Under R}

/-- Only the two geometric totals and their original chart equation enter the carrier. -/
structure Geometry where
  /-- The total geometric map between the polynomial coefficient fibers. -/
  polynomial : space (op P, (polynomialUnderFunctor R).obj c) ⟶
    space (op P, (polynomialUnderFunctor R).obj a)
  /-- The total geometric map between the underlying coefficient fibers. -/
  coefficient : space (op P, c) ⟶ space (op P, a)
  comm : (laurentPlus P c ≫ polynomial) ≫ polynomialProjection P a =
    laurentProjection P c ≫ coefficient

namespace Geometry
variable (D : Geometry P (a := a) (c := c))

/-- Normalized polynomial total, with its unchanged source projection. -/
abbrev polyRef := BassOverlap.projectionMap P (a := a) ≫
  BassH0Merge.normalizedMap D.polynomial
/-- Normalized Laurent total. -/
abbrev laurentRef := BassH0Merge.normalizedMap (laurentProjection P c ≫ D.coefficient)
/-- The exact original geometric transport and binary normalization isomorphism. -/
def ordinary : (laurentRef P D).functor ≅
    (polyRef P D ≫ chartMap P (c := c)).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback D.comm.symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (laurentPlus P c ≫ D.polynomial) (polynomialProjection P a)) AsSmall.up) ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (BinaryNormalizationSimplex.total (laurentPlus P c) D.polynomial)
/-- The same forward inner Laurent unit at the complete geometric total. -/
def unit : (laurentRef P D).functor ≅ (laurentRef P D).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedFlatPullbackNormalizationIso
      (laurentProjection P c ≫ D.coefficient)).symm ≪≫
      boundedFlatPerfectPullbackUnitIso
        (laurentProjection P c ≫ D.coefficient)
        (LaurentUnitReferenceSpecialization.laurentUnit P c) ≪≫
      boundedFlatPullbackNormalizationIso
        (laurentProjection P c ≫ D.coefficient)) AsSmall.up)
/-- The full shifted anchor retains its original left action. -/
abbrev shifted := unit P D ≪≫ ordinary P D
/-- The same two-tip carrier, expressed using just its geometric totals. -/
abbrev carrier := CommonReferenceNerve.CutOpenCarrier.space
  (polyRef P D) (chartMap P (c := c)) (laurentRef P D) (ordinary P D) (shifted P D)
/-- The unchanged original native evaluator. -/
abbrev evaluate (n : ℕ) := CommonReferenceNerve.CutOpenCarrier.nativeEval
  (polyRef P D) (chartMap P (c := c)) (laurentRef P D) (ordinary P D) (shifted P D) n
/-- The ordinary and shifted tips are still distinct. -/
abbrev minusTip := CommonReferenceNerve.CutOpenCarrier.tipMinus
  (polyRef P D) (chartMap P (c := c)) (laurentRef P D) (ordinary P D) (shifted P D)
/-- The tip of the polynomial attachment defined by the shifted anchor. -/
abbrev plusTip := CommonReferenceNerve.CutOpenCarrier.tipPlus
  (polyRef P D) (chartMap P (c := c)) (laurentRef P D) (ordinary P D) (shifted P D)

/-- The chart equation is a proof; neither reference isomorphism is discarded. -/
theorem ext_totals {D E : Geometry P (a := a) (c := c)}
    (hp : D.polynomial = E.polynomial) (hc : D.coefficient = E.coefficient) : D = E := by
  cases D
  cases E
  cases hp
  cases hc
  rfl

end Geometry

variable {b b' : Under R} (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The original factorization supplies these literal two geometric composites. -/
def geometry : Geometry P (a := a) (c := c) where
  polynomial := coefficientMap P ((polynomialUnderFunctor R).map q) ≫
    coefficientMap P ((polynomialUnderFunctor R).map p)
  coefficient := coefficientMap P q ≫ coefficientMap P p
  comm := BassOverlap.chart_total P p q (underToLaurent R) (laurentPlus_projection P c)

/-- Equal coefficient composites give equal full geometric data. -/
theorem geometry_eq (h : p ≫ q = p' ≫ q') : geometry P p q = geometry P p' q' := by
  apply Geometry.ext_totals
  · simp only [geometry, ← coefficientMap_comp, ← Functor.map_comp, h]
  · simp only [geometry, ← coefficientMap_comp, h]

/-- The actual polynomial reference is precisely the geometric normal form. -/
theorem polynomial_normal_form :
    polynomialReference P p q = Geometry.polyRef P (geometry P p q) := rfl

/-- The actual Laurent reference is precisely the geometric normal form. -/
theorem laurent_normal_form :
    laurentReference P p q = Geometry.laurentRef P (geometry P p q) := rfl

/-- The ordinary anchor keeps its entire original normalization route. -/
theorem ordinary_normal_form :
    HEq (ordinaryAnchor P p q) (Geometry.ordinary P (geometry P p q)) := HEq.rfl

/-- The shifted anchor keeps the original forward-unit left action. -/
theorem shifted_normal_form :
    HEq (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (Geometry.shifted P (geometry P p q)) := HEq.rfl

/-- The full carrier, with both attachments, is precisely its geometric normal form. -/
theorem carrier_normal_form :
    CoefficientBassPositiveC0CarrierSeed.Carrier P p q =
      Geometry.carrier P (geometry P p q) := rfl

/-- The whole native family has the same geometric normal form at every level. -/
theorem native_normal_form (n : ℕ) :
    HEq (CommonReferenceNerve.CutOpenCarrier.nativeEval
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
      (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n)
      (Geometry.evaluate P (geometry P p q) n) := HEq.rfl

/-- The ordinary tip is retained before any native evaluation. -/
theorem minus_normal_form : HEq (CoefficientBassPositiveC0CarrierSeed.minusTip P p q)
    (Geometry.minusTip P (geometry P p q)) := HEq.rfl

/-- The shifted tip is retained independently of the ordinary tip. -/
theorem plus_normal_form : HEq (CoefficientBassPositiveC0CarrierSeed.plusTip P p q)
    (Geometry.plusTip P (geometry P p q)) := HEq.rfl

end Quillen.PerfectComplexes.CoefficientBassNegativeCarrierReference
