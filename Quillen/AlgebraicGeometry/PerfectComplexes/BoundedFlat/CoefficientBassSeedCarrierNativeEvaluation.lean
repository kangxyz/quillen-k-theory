/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassCutOpenAugmentationRecovery
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierAugmentation

/-! The actual augmented seed carrier evaluates in the original full Bass cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassSeedCarrierAugmentation
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassSeedCarrierLaurentReference
open BassProjectionPath.WholeReference.FourEdge
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- All full scalar points and all genuine native inputs are retained. -/
def nativeEval (n : ℕ) : space P p q →
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space (op P, a)))).space n →
    (nativeBassCone P c).space n :=
  augmentedEval P c (inputReference P p q) (polynomialReference P p q)
    (laurentReference P p q) (referenceIso P p q) (ordinaryAnchor P p q)
    (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n

/-- The entire original filled carrier has its exact original native image. -/
theorem nativeEval_originalMap (n : ℕ)
    (y : CoefficientBassPositiveC0CarrierSeed.Carrier P p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space (op P, a)))).space n) :
    nativeEval P p q n (originalMap P p q y) x =
      (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
        (CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
          (laurentReference P p q) (ordinaryAnchor P p q)
          (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n y x) :=
  augmentedEval_originalMap P c (inputReference P p q) (polynomialReference P p q)
    (laurentReference P p q) (referenceIso P p q) (ordinaryAnchor P p q)
    (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n y x

/-- Every compact scalar family is jointly continuous with its independent native input. -/
theorem nativeEval_compact_continuous {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (f : C(S, space P p q)) (n : ℕ) :
    Continuous (fun z : S × (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space (op P, a)))).space n ↦
      nativeEval P p q n (f z.1) z.2) :=
  augmentedEval_compact_continuous P c (inputReference P p q) (polynomialReference P p q)
    (laurentReference P p q) (referenceIso P p q) (ordinaryAnchor P p q)
    (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) f n

end Quillen.PerfectComplexes.CoefficientBassSeedCarrierAugmentation
