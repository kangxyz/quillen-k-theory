/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0UnitNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupport

/-!
# Exact original native recovery of the literal C0 carrier seed face

The same original half-null and nested seed concatenations are evaluated at unchanged
parameters. The lower owner supplies the actual continuous two-tip face; this owner recovers
its original supported seed, for all levels including zero, without a filler hypothesis.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u v w z
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierSeedNative
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment CoefficientBassPositiveC0CarrierRails
open CoefficientBassPositiveC0CarrierNative CoefficientBassPositiveC0UnitNative
open CoefficientBassPositiveC0CarrierSeed

/-- Generic pointwise functoriality of the literal original half-time concatenation. -/
private theorem mapped_trans {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f g h : C(X, Y)} {f' g' h' : C(X', Y')}
    (H : f.Homotopy g) (K : g.Homotopy h)
    (H' : f'.Homotopy g') (K' : g'.Homotopy h')
    (φ : Y → Y') (x : X) (x' : X')
    (hH : ∀ t : I, φ (H (t, x)) = H' (t, x'))
    (hK : ∀ t : I, φ (K (t, x)) = K' (t, x')) (s : I) :
    φ ((H.trans K) (s, x)) = (H'.trans K') (s, x') := by
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · exact hH _
  · exact hK _

/-- Native trans has the identical pointwise half-time concatenation of its whole levels. -/
private theorem native_trans_apply {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
    (H : Homotopy f g) (K : Homotopy g h) (n : ℕ) (s : I) (x : E.space n) :
    (((H.levelHomotopy n).toHomotopy.trans (K.levelHomotopy n).toHomotopy) (s, x)) =
      (H.trans K).level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

abbrev evaluate (n : ℕ) := CutOpenCarrier.nativeEval
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n

abbrev originalProjection := (boundedFlatCoefficientLaurentPlusHomotopy P c).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c)))
abbrev originalContraction := Homotopy.precomp
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
  (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P c)))
abbrev originalUnit := (boundedFlatCoefficientLaurentUnitHomotopy P c).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c)))

variable (n : ℕ) (r s : I)
  (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)

theorem projectionMinus_native : evaluate P p q n (projectionMinus P p q (s, r)) x =
    (originalProjection P (c := c)).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (positiveProjectionParameter P p q (r, s))) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion,
    pointwisePrespectrumFamily_eq_compact _ (positiveProjectionParameter P p q),
    positiveProjectionParameter_native]
  rfl

theorem projectionPlus_native : evaluate P p q n (projectionPlus P p q (s, r)) x =
    (originalProjection P (c := c)).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (shiftedProjectionParameter P p q (r, s))) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion,
    pointwisePrespectrumFamily_eq_compact _ (shiftedProjectionParameter P p q),
    shiftedProjectionParameter_native]
  rfl

theorem contractionMinus_native : evaluate P p q n (contractionMinus P p q (s, r)) x =
    (originalContraction P (c := c)).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  cylinderMinus_native P p q n r s x

theorem contractionPlus_native : evaluate P p q n (contractionPlus P p q (s, r)) x =
    (originalContraction P (c := c)).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  cylinderPlus_native P p q n r s x

/-- The entire ordinary null, with the same original half-time cut. -/
theorem nullMinus_native : evaluate P p q n (nullMinus P p q (s, r)) x =
    (boundedFlatCoefficientBassPositiveConeNull P c).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  mapped_trans (projectionMinus P p q) (contractionMinus P p q)
    ((originalProjection P (c := c)).levelHomotopy n).toHomotopy
    ((originalContraction P (c := c)).levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) r
    ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))
    (fun t ↦ projectionMinus_native P p q n r t x)
    (fun t ↦ contractionMinus_native P p q n r t x) s

/-- The entire separately shifted null has the same native value, not the same carrier tip. -/
theorem nullPlus_native : evaluate P p q n (nullPlus P p q (s, r)) x =
    (boundedFlatCoefficientBassPositiveConeNull P c).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  mapped_trans (projectionPlus P p q) (contractionPlus P p q)
    ((originalProjection P (c := c)).levelHomotopy n).toHomotopy
    ((originalContraction P (c := c)).levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) r
    ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))
    (fun t ↦ projectionPlus_native P p q n r t x)
    (fun t ↦ contractionPlus_native P p q n r t x) s

/-- The forward unit uses the original normalized native unit, at unchanged independent time. -/
theorem forwardUnit_native : evaluate P p q n (forwardUnit P p q (s, r)) x =
    (originalUnit P (c := c)).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _
      (CoefficientBassPositiveC0UnitStrip.unitProductParameter P p q (r, s))) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion,
    pointwisePrespectrumFamily_eq_compact _
      (CoefficientBassPositiveC0UnitStrip.unitProductParameter P p q),
    unitProductParameter_native]
  rfl

/-- Exact entire original seed recovery, with all nested trans/symm subdivisions unchanged. -/
theorem face_native : evaluate P p q n (face P p q (r, s)) x =
    Path.toContinuousMap ((boundedFlatCoefficientBassPositiveConeSeed P c).map n
      ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))) s := by
  let N := boundedFlatCoefficientBassPositiveConeNull P c
  let U := originalUnit P (c := c)
  change evaluate P p q n
    (((nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))) (s, r)) x =
      (N.symm.trans (U.trans N)).level n
        (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))
  refine (mapped_trans (nullMinus P p q).symm
    ((forwardUnit P p q).trans (nullPlus P p q))
    ((N.symm).levelHomotopy n).toHomotopy ((U.trans N).levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) r
    ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) ?_ ?_ s).trans
      (native_trans_apply N.symm (U.trans N) n s
        ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)))
  · intro t
    exact nullMinus_native P p q n r (unitInterval.symm t) x
  · intro t
    exact mapped_trans (forwardUnit P p q) (nullPlus P p q)
      (U.levelHomotopy n).toHomotopy (N.levelHomotopy n).toHomotopy
      (fun y ↦ evaluate P p q n y x) r
      ((boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x))
      (fun v ↦ forwardUnit_native P p q n r v x)
      (fun v ↦ nullPlus_native P p q n r v x) t

/-- The actual p;q=l coefficient source cast is retained in the whole supported C0 face. -/
theorem actual_reversed_face_native (d : Under R) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    evaluate P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) n
      (reversedFace P ((polynomialUnderCoefficient R).app d)
        ((underToLaurent R).app d) (r, s)) x =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj d)).map n
        (((boundedFlatCoefficientLaurentPlusHomotopy P d).symm).level n (r, x))) s :=
  face_native P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
    n (unitInterval.symm r) s x

/-- The native face is exactly the original first C0 segment in supportedRight, unretimed. -/
theorem actual_original_C0 (d : Under R) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    evaluate P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) n
      (reversedFace P ((polynomialUnderCoefficient R).app d)
        ((underToLaurent R).app d) (r, s)) x =
    Path.toContinuousMap
      ((((boundedFlatCoefficientLaurentPlusHomotopy P d).postcomp
        (boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj d))).symm).level
          n (r, x)) s :=
  actual_reversed_face_native P d n r s x

end Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierSeedNative
