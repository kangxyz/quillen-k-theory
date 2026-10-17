/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputSecond

/-! The whole second height half evaluates to K on the unchanged original span-map image. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputSecond
open BassH0Merge BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "Jb" => normalizedMap (polynomialProjection P b)
local notation "H" => boundedFlatCoefficientPolynomialSquareHomotopy P p
local notation "M" => boundedFlatCoefficientPolynomialSpanMap P p

private theorem span_first (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (M).map n (input P (a := a) n (lower t) x) =
      (HomotopyPushout.inl (prespectrumMap Jb) (prespectrumMap Jb)).map n
        ((H).level n (t, x)) :=
  HomotopyPushout.mapOfHomotopies_first_half _ _ _ _ _ _ _ _ _ n t x

private theorem span_middle (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (M).map n (input P (a := a) n (upper (lower t)) x) =
      input P (a := b) n t ((prespectrumMap (normalizedMap (coefficientMap P p))).map n x) := by
  let A := (H).postcomp (HomotopyPushout.inl (prespectrumMap Jb) (prespectrumMap Jb))
  let K := Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
    (HomotopyPushout.glue (prespectrumMap Jb) (prespectrumMap Jb))
  let L := (H).symm.postcomp (HomotopyPushout.inr (prespectrumMap Jb) (prespectrumMap Jb))
  exact (Homotopy.trans_upper_cell A (K.trans L) n (lower t) x).trans
    (Homotopy.trans_lower_cell K L n t x)

private theorem span_last (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (M).map n (input P (a := a) n (upper (upper t)) x) =
      (HomotopyPushout.inr (prespectrumMap Jb) (prespectrumMap Jb)).map n
        ((H).level n (unitInterval.symm t, x)) := by
  let A := (H).postcomp (HomotopyPushout.inl (prespectrumMap Jb) (prespectrumMap Jb))
  let K := Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
    (HomotopyPushout.glue (prespectrumMap Jb) (prespectrumMap Jb))
  let L := (H).symm.postcomp (HomotopyPushout.inr (prespectrumMap Jb) (prespectrumMap Jb))
  exact (Homotopy.trans_upper_cell A (K.trans L) n (upper t) x).trans
    (Homotopy.trans_upper_cell K L n t x)

/-- All comparison, height, overlap and native structure clocks remain independent. -/
theorem family_native (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d (TripleLaurent.input P p q w) n (family P p q w (r, (h, t))) x =
      (BassMWhole.coneComposition P q w).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P b).map n)
          (h, (M).map n (input P (a := a) n t x))) := by
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [family_lower, InputPolynomial.plusFamily_native, span_first]; rfl
  · rw [family_middle, InputCentral.family_native, span_middle]
  · rw [family_upper, InputPolynomial.minusFamily_native, span_last]; rfl

/-- This is precisely the second original outer-height half of K after B(p). -/
theorem family_native_upper (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d (TripleLaurent.input P p q w) n (family P p q w (r, (h, t))) x =
      (BassMWhole.coneComposition P q w).level n
        (r, (boundedFlatCoefficientBassConeMap P p).map n
          (ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
            (upper h, input P (a := a) n t x))) := by
  rw [boundedFlatCoefficientBassConeMap_cylinder, Homotopy.trans_upper_cell]
  exact family_native P p q w n r h t x

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputSecond
