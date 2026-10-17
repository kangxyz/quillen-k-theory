/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeGeometricCarrier

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
variable {a b b' c : Under R} (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The polynomial reference retains the normalization of the complete geometric composite. -/
theorem polynomial_reference_eq (h : p ≫ q = p' ≫ q') :
    polynomialReference P p q = polynomialReference P p' q' :=
  (polynomial_normal_form P p q).trans
    ((congrArg (a₁ := geometry P p q) (a₂ := geometry P p' q')
      (fun D : Geometry P (a := a) (c := c) ↦ Geometry.polyRef P D)
      (geometry_eq P p q p' q' h)).trans (polynomial_normal_form P p' q').symm)

/-- The Laurent reference retains the same complete geometric total. -/
theorem laurent_reference_eq (h : p ≫ q = p' ≫ q') :
    laurentReference P p q = laurentReference P p' q' :=
  (laurent_normal_form P p q).trans
    ((congrArg (a₁ := geometry P p q) (a₂ := geometry P p' q')
      (fun D : Geometry P (a := a) (c := c) ↦ Geometry.laurentRef P D)
      (geometry_eq P p q p' q' h)).trans (laurent_normal_form P p' q').symm)

/-- Both original attachment isomorphisms are retained in the equality of the whole carrier. -/
theorem carrier_eq (h : p ≫ q = p' ≫ q') :
    CoefficientBassPositiveC0CarrierSeed.Carrier P p q =
      CoefficientBassPositiveC0CarrierSeed.Carrier P p' q' :=
  (carrier_normal_form P p q).trans
    ((congrArg (a₁ := geometry P p q) (a₂ := geometry P p' q')
      (fun D : Geometry P (a := a) (c := c) ↦ Geometry.carrier P D)
      (geometry_eq P p q p' q' h)).trans (carrier_normal_form P p' q').symm)

/-- Transport along equality of topological spaces is continuous. -/
def topologicalCast (X Y : TopCat.{v}) (e : X = Y) : C(X, Y) where
  toFun x := cast (congrArg (fun Z : TopCat.{v} ↦ (Z : Type v)) e) x
  continuous_toFun := by
    subst Y
    exact continuous_id

/-- Equality transport keeps the underlying point heterogeneously unchanged. -/
theorem topologicalCast_heq (X Y : TopCat.{v}) (e : X = Y) (x : X) :
    HEq (topologicalCast X Y e x) x :=
  cast_heq (congrArg (fun Z : TopCat.{v} ↦ (Z : Type v)) e) x

/-- Equality of all carrier data induces a continuous map preserving the actual topology. -/
abbrev transport (h : p ≫ q = p' ≫ q') :
    C(CoefficientBassPositiveC0CarrierSeed.Carrier P p q,
      CoefficientBassPositiveC0CarrierSeed.Carrier P p' q') :=
  topologicalCast (CoefficientBassPositiveC0CarrierSeed.Carrier P p q)
    (CoefficientBassPositiveC0CarrierSeed.Carrier P p' q') (carrier_eq P p q p' q' h)

/-- The transport changes only the dependent carrier type. -/
theorem transport_heq (h : p ≫ q = p' ≫ q')
    (z : CoefficientBassPositiveC0CarrierSeed.Carrier P p q) :
    HEq (transport P p q p' q' h z) z :=
  cast_heq (congrArg (fun Z : TopCat ↦ (Z : Type _)) (carrier_eq P p q p' q' h)) z

/-- The entire native family retains both attachment isomorphisms under the same equality. -/
theorem native_family_heq (h : p ≫ q = p' ≫ q') (n : ℕ) :
    HEq (CommonReferenceNerve.CutOpenCarrier.nativeEval
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
      (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n)
      (CommonReferenceNerve.CutOpenCarrier.nativeEval
        (polynomialReference P p' q') (chartMap P (c := c)) (laurentReference P p' q')
        (ordinaryAnchor P p' q') (LaurentUnitReferenceSpecialization.shiftedAnchor P p' q') n) := by
  have aux (D E : Geometry P (a := a) (c := c)) (h : D = E) :
      HEq (Geometry.evaluate P D n) (Geometry.evaluate P E n) := by
    subst E
    rfl
  exact (native_normal_form P p q n).trans
    ((aux (geometry P p q) (geometry P p' q') (geometry_eq P p q p' q' h)).trans
      (native_normal_form P p' q' n).symm)

private theorem value_heq {X Y : Type v} {Z : Type*} (f : X → Z) (g : Y → Z)
    (hf : HEq f g) {x : X} {y : Y} (hx : HEq x y) : f x = g y := by
  have ht := type_eq_of_heq hx
  subst Y
  cases hf
  exact congrArg f (eq_of_heq hx)

/-- Every native level and input is preserved by the full-reference carrier transport. -/
theorem transport_native (h : p ≫ q = p' ≫ q') (n : ℕ)
    (z : CoefficientBassPositiveC0CarrierSeed.Carrier P p q)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CommonReferenceNerve.CutOpenCarrier.nativeEval
        (polynomialReference P p' q') (chartMap P (c := c)) (laurentReference P p' q')
        (ordinaryAnchor P p' q') (LaurentUnitReferenceSpecialization.shiftedAnchor P p' q') n
        (transport P p q p' q' h z) x =
      CommonReferenceNerve.CutOpenCarrier.nativeEval
        (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
        (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n z x :=
  congrFun (value_heq _ _ (native_family_heq P p q p' q' h n).symm
    (transport_heq P p q p' q' h z)) x

/-- The ordinary tip keeps its own identity through the full-reference transport. -/
theorem transport_minusTip (h : p ≫ q = p' ≫ q') :
    transport P p q p' q' h (CoefficientBassPositiveC0CarrierSeed.minusTip P p q) =
      CoefficientBassPositiveC0CarrierSeed.minusTip P p' q' := by
  apply eq_of_heq
  refine (transport_heq P p q p' q' h _).trans ?_
  have aux (D E : Geometry P (a := a) (c := c)) (h : D = E) :
      HEq (Geometry.minusTip P D) (Geometry.minusTip P E) := by
    subst E
    rfl
  exact (minus_normal_form P p q).trans
    ((aux (geometry P p q) (geometry P p' q') (geometry_eq P p q p' q' h)).trans
      (minus_normal_form P p' q').symm)

/-- The shifted tip stays separate and is transported with the forward inner-unit anchor. -/
theorem transport_plusTip (h : p ≫ q = p' ≫ q') :
    transport P p q p' q' h (CoefficientBassPositiveC0CarrierSeed.plusTip P p q) =
      CoefficientBassPositiveC0CarrierSeed.plusTip P p' q' := by
  apply eq_of_heq
  refine (transport_heq P p q p' q' h _).trans ?_
  have aux (D E : Geometry P (a := a) (c := c)) (h : D = E) :
      HEq (Geometry.plusTip P D) (Geometry.plusTip P E) := by
    subst E
    rfl
  exact (plus_normal_form P p q).trans
    ((aux (geometry P p q) (geometry P p' q') (geometry_eq P p q p' q' h)).trans
      (plus_normal_form P p' q').symm)

end Quillen.PerfectComplexes.CoefficientBassNegativeCarrierReference
