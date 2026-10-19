/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFinePerfectConnecting

/-!
Original perfect classes and the intrinsic fine boundary retain their geometric
sign, the original supported K-zero endpoint, and the geometric exactness kernel.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u

namespace QuillenTest.CoefficientFinePerfectConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The K1 boundary lands in the original supported K-zero comparison used by negative recursion. -/
theorem fine_Kone_boundary_original_Kzero
    (a : Under R)
    (x : PerfectK (space (op P, a)) (0 + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientFineLocalizationConnecting f a ((0 : ℕ) : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a))
          (show ((0 + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl))
          ((stableHomotopyFunctor ((0 + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a)
            (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) (0 + 1)
              (Additive.ofMul x)))) =
      -((stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        ((boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom
          (Additive.ofMul (qcqsPerfectConnectingHom (schemeMap f a) 0 x)))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have hs := boundedFlatCoefficientFineConnecting_perfectClass_sign f a 0 rfl x
  dsimp only at hs ⊢
  simpa only [boundedFlatCoefficientSupportedKStableEquiv_zero] using hs

end QuillenTest.CoefficientFinePerfectConnecting
