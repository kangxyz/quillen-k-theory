/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenModels
public import Quillen.Waldhausen.SConstruction.Iterated.ModelStableHomotopy

/-! # The original perfect supported groups at the three auxiliary endpoints

These are original supported evaluation followed by the original perfect inclusion.
Only compactness of the ambient schemes is needed, not compactness of the support opens.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original fiber evaluation and perfect inclusion, with the union support unchanged. -/
def auxiliaryFiberPerfectKEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n ≃*
      PerfectSupportedK (boundedFlatCoefficientFiberSupportOpen f T a).ι n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedFlatCoefficientSupportedSectionKEquiv
    (boundedFlatCoefficientFiberSupportOpen f T a).ι n).trans
    (boundedFlatPerfectSupportedKEquiv (boundedFlatCoefficientFiberSupportOpen f T a).ι n)

/-- The original ambient supported evaluation and perfect inclusion. -/
def auxiliaryAmbientPerfectKEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.K n ≃*
      PerfectSupportedK (boundedFlatCoefficientSupportOpen Q T a).ι n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedFlatCoefficientSupportedSectionKEquiv
    (boundedFlatCoefficientSupportOpen Q T a).ι n).trans
    (boundedFlatPerfectSupportedKEquiv (boundedFlatCoefficientSupportOpen Q T a).ι n)

/-- The original full-open perfect comparison retains the inverse-image support. -/
def auxiliaryOpenPerfectKEquiv [CompactSpace P.left] (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedFullOpenModel f T a).waldhausen.K n ≃*
      PerfectSupportedK (boundedFlatCoefficientOpenSupportOpen f T a).ι n :=
  boundedFlatCoefficientSupportedFullOpenPerfectKEquiv f T a n

/-- Original fiber perfect classes in the unchanged fine model spectrum. -/
def auxiliaryFiberPerfectStableEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :=
  (auxiliaryFiberPerfectKEquiv f T a n).symm.toAdditive.trans
    (modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n)

/-- Original ambient perfect classes in the unchanged fine model spectrum. -/
def auxiliaryAmbientPerfectStableEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :=
  (auxiliaryAmbientPerfectKEquiv T a n).symm.toAdditive.trans
    (modelKStableEquiv (boundedFlatCoefficientSupportedAmbientModel T a) n)

/-- Original full-open perfect classes in the unchanged fine model spectrum. -/
def auxiliaryOpenPerfectStableEquiv [CompactSpace P.left] (a : Under R) (n : ℕ) :=
  (auxiliaryOpenPerfectKEquiv f T a n).symm.toAdditive.trans
    (modelKStableEquiv (boundedFlatCoefficientSupportedFullOpenModel f T a) n)

/-- Evaluation retains every original fiber model representative. -/
theorem auxiliaryFiberPerfectStableEquiv_evaluation [CompactSpace Q.left]
    (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n) :
    auxiliaryFiberPerfectStableEquiv f T a n
        (Additive.ofMul (auxiliaryFiberPerfectKEquiv f T a n x)) =
      modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n
        (Additive.ofMul x) := by
  change modelKStableEquiv _ n (Additive.ofMul
    ((auxiliaryFiberPerfectKEquiv f T a n).symm
      (auxiliaryFiberPerfectKEquiv f T a n x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Evaluation retains every original ambient model representative. -/
theorem auxiliaryAmbientPerfectStableEquiv_evaluation [CompactSpace Q.left]
    (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.K n) :
    auxiliaryAmbientPerfectStableEquiv T a n
        (Additive.ofMul (auxiliaryAmbientPerfectKEquiv T a n x)) =
      modelKStableEquiv (boundedFlatCoefficientSupportedAmbientModel T a) n
        (Additive.ofMul x) := by
  change modelKStableEquiv _ n (Additive.ofMul
    ((auxiliaryAmbientPerfectKEquiv T a n).symm
      (auxiliaryAmbientPerfectKEquiv T a n x))) = _
  rw [MulEquiv.symm_apply_apply]

omit [IsOpenImmersion f.left] in
/-- Evaluation retains every original full-open model representative. -/
theorem auxiliaryOpenPerfectStableEquiv_evaluation [CompactSpace P.left]
    (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedFullOpenModel f T a).waldhausen.K n) :
    auxiliaryOpenPerfectStableEquiv f T a n
        (Additive.ofMul (auxiliaryOpenPerfectKEquiv f T a n x)) =
      modelKStableEquiv (boundedFlatCoefficientSupportedFullOpenModel f T a) n
        (Additive.ofMul x) := by
  change modelKStableEquiv _ n (Additive.ofMul
    ((auxiliaryOpenPerfectKEquiv f T a n).symm
      (auxiliaryOpenPerfectKEquiv f T a n x))) = _
  rw [MulEquiv.symm_apply_apply]

end Quillen.PerfectComplexes
