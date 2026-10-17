/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKZeroComparison

/-!
# Original supported K-groups in the same native fine section spectrum

Original supported evaluation and the actual model K/stable equivalence give the
comparison in every nonnegative degree, naturally for each original coefficient
pair pullback. The comparison retains the original perfect K-groups and the
unchanged fine section prespectrum. Only ambient compactness is required here.
Compatibility with degree-raising scalar self-track operations requires an actual
unit-preserving evaluation square and is not a consequence of this ordinary-map
naturality theorem.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Original supported K-theory computes the same actual fine section stable group. -/
def boundedFlatCoefficientSupportedKStableEquiv (a : Under R) (n : ℕ) :
    Additive (PerfectSupportedK (schemeMap f a) n) ≃+
      stableHomotopyGroup ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj a)
        (n : ℤ) :=
  (boundedFlatCoefficientSupportedPerfectKEquiv f a n).symm.toAdditive.trans
    (modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) n)

/-- The original evaluation representative maps to the original model stable representative. -/
theorem boundedFlatCoefficientSupportedKStableEquiv_evaluation (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedModel f a).waldhausen.K n) :
    boundedFlatCoefficientSupportedKStableEquiv f a n
        (Additive.ofMul (boundedFlatCoefficientSupportedPerfectKEquiv f a n x)) =
      modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) n (Additive.ofMul x) := by
  change modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) n
    (Additive.ofMul ((boundedFlatCoefficientSupportedPerfectKEquiv f a n).symm
      (boundedFlatCoefficientSupportedPerfectKEquiv f a n x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Naturality preserves the original coefficient pair pullback and unchanged model map. -/
theorem boundedFlatCoefficientSupportedKStableEquiv_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (x : PerfectSupportedK (schemeMap f a) n) :
    boundedFlatCoefficientSupportedKStableEquiv f b n
      (Additive.ofMul (perfectSupportedKPullback
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).map g).unop n x)) =
    (stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedPrespectrumFunctor f).map g)
      (boundedFlatCoefficientSupportedKStableEquiv f a n (Additive.ofMul x)) := by
  obtain ⟨y, rfl⟩ := (boundedFlatCoefficientSupportedPerfectKEquiv f a n).surjective x
  rw [← boundedFlatCoefficientSupportedPerfectKEquiv_naturality,
    boundedFlatCoefficientSupportedKStableEquiv_evaluation,
    boundedFlatCoefficientSupportedKStableEquiv_evaluation]
  exact modelKStableEquiv_naturality (boundedFlatCoefficientSupportedModelMap f g) n y

/-- Degree zero is exactly the established comparison used by the original negative recursion. -/
theorem boundedFlatCoefficientSupportedKStableEquiv_zero (a : Under R)
    (x : PerfectSupportedK (schemeMap f a) 0) :
    boundedFlatCoefficientSupportedKStableEquiv f a 0 (Additive.ofMul x) =
      (boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom (Additive.ofMul x) := rfl

end Quillen.PerfectComplexes
