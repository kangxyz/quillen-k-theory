/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedConnectiveInvertibility

/-! # The inverse original supported seed is natural in every coefficient map -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The pointwise result supplies a natural inverse to the unchanged original seed. -/
example (n : ℕ) {a b : Under R} (g : a ⟶ b) :
    (boundedFlatCoefficientSupportedBassDiagram f 1 ⋙ stableHomotopyFunctor (n : ℤ)).map g ≫
        inv ((stableHomotopyFunctor (n : ℤ)).map
          ((boundedFlatCoefficientSupportedBassTransition f 0).app b)) =
      inv ((stableHomotopyFunctor (n : ℤ)).map
          ((boundedFlatCoefficientSupportedBassTransition f 0).app a)) ≫
        (boundedFlatCoefficientSupportedBassDiagram f 0 ⋙ stableHomotopyFunctor (n : ℤ)).map g := by
  let τ := Functor.whiskerRight (boundedFlatCoefficientSupportedBassTransition f 0)
    (stableHomotopyFunctor (n : ℤ))
  let : ∀ a, IsIso (τ.app a) := fun a =>
    boundedFlatCoefficientSupportedBassTransition_zero_connective_isIso f a n
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  simpa only [NatIso.isIso_inv_app, τ, Functor.whiskerRight_app] using (inv τ).naturality g
