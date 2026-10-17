/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFaceNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily

/-!
# The genuine C1 face as a continuous based-loop family

Compact carrier evaluation supplies joint continuity. Only after the separate tip images are
identified with the native basepoint do we curry the seed coordinate into a based loop.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1SeedFaceLoopFamily
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment CoefficientBassPositiveC1SeedFace
open CoefficientBassPositiveC1SeedFaceNative
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The unchanged original source, including its genuine loop input at degree zero. -/
abbrev source := prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
/-- The actual native target cone, before parameter looping. -/
abbrev target := CutOpenCarrier.nativeCone (chartMap P (c := c))

/-- Joint evaluation of both compact face coordinates and the whole original input. -/
def joint (n : ℕ) : C((I × I) × (source P (a := a)).space n,
    (target P (c := c)).space n) :=
  CutOpenCarrier.compactNativeFamily
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    (face P p q) n

/-- The compact packaging preserves every scalar face value and the whole input. -/
theorem joint_apply (n : ℕ) (r s : I) (x : (source P (a := a)).space n) :
    joint P p q n ((r, s), x) = evaluate P p q n (face P p q (r, s)) x := rfl

/-- Curry only the evaluated face; the carrier's two tips themselves remain distinct. -/
def loopFamily (n : ℕ) : C(I × (source P (a := a)).space n,
    (parameterLooping (target P (c := c))).space n) where
  toFun z :=
    { toFun s := joint P p q n ((z.1, s), z.2)
      continuous_toFun := by fun_prop
      source' := face_bottom_native P p q n z.1 z.2
      target' := face_top_native P p q n z.1 z.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × (source P (a := a)).space n) × I ↦
      joint P p q n ((z.1.1, z.2), z.1.2))
    fun_prop

/-- Composition and seed coordinates stay independent under currying. -/
theorem loopFamily_apply (n : ℕ) (r s : I) (x : (source P (a := a)).space n) :
    Path.toContinuousMap (loopFamily P p q n (r, x)) s =
      evaluate P p q n (face P p q (r, s)) x := rfl

/-- The exact original step-composition acts on the genuine seed, at every degree. -/
theorem loopFamily_native (n : ℕ) (r : I) (x : (source P (a := a)).space n) :
    loopFamily P p q n (r, x) =
      (CoefficientBassPositiveCompositionTrack.stepComposition P p q).level n
        (r, (boundedFlatCoefficientBassPositiveConeSeed P a).map n x) := by
  apply Path.ext
  funext s
  exact face_native P p q n r s x

/-- The based input gives the constant output loop for every composition coordinate. -/
theorem loopFamily_point (n : ℕ) (r : I) :
    loopFamily P p q n (r, (source P (a := a)).point n) =
      (parameterLooping (target P (c := c))).point n := by
  apply Path.ext
  funext s
  exact CutOpenCarrier.compactNativeFamily_point
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    (face P p q) n (r, s)

/-- Structure time is external to both composition time and the seed-path coordinate. -/
theorem loopFamily_structure (n : ℕ) (r : I)
    (x : (source P (a := a)).space n) (t : I) :
    loopFamily P p q (n + 1) (r, (source P (a := a)).structureMap n x t) =
      (parameterLooping (target P (c := c))).structureMap n
        (loopFamily P p q n (r, x)) t := by
  apply Path.ext
  funext s
  exact CutOpenCarrier.compactNativeFamily_structure
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    (face P p q) n (r, s) x t

/-- Degree zero receives the entire original loop, with no sampling of its input time. -/
theorem loopFamily_zero (r : I)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    loopFamily P p q 0 (r, γ) =
      (CoefficientBassPositiveCompositionTrack.stepComposition P p q).level 0
        (r, (boundedFlatCoefficientBassPositiveConeSeed P a).map 0 γ) :=
  loopFamily_native P p q 0 r γ

end Quillen.PerfectComplexes.CoefficientBassPositiveC1SeedFaceLoopFamily
