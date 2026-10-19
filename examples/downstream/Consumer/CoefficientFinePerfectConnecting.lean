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

namespace Consumer.CoefficientFinePerfectConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The genuine fine boundary kills classes in the original geometric ambient restriction image. -/
theorem fineBoundary_originalAmbientRestriction_eq_zero
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectK (space (op Q, a)) (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientFineLocalizationConnecting f a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)) κ)
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a)
            (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) (n + 1)
              (Additive.ofMul (perfectKRestrict (schemeMap f a) (n + 1) x))))) = 0 := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  dsimp only
  have hm : perfectKRestrict (schemeMap f a) (n + 1) x ∈
      (perfectKRestrict (schemeMap f a) (n + 1)).range := ⟨x, rfl⟩
  rw [range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom (schemeMap f a) n] at hm
  have hz : qcqsPerfectConnectingHom (schemeMap f a) n
      (perfectKRestrict (schemeMap f a) (n + 1) x) = 1 := hm
  have hs := boundedFlatCoefficientFineConnecting_perfectClass_sign f a n κ
    (perfectKRestrict (schemeMap f a) (n + 1) x)
  dsimp only at hs
  rw [hz, ofMul_one, map_zero, map_zero, neg_zero] at hs
  exact hs

end Consumer.CoefficientFinePerfectConnecting
