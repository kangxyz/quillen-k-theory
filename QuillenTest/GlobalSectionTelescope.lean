/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionTelescope

/-! # Actual ambient telescope comparison regressions -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex Quillen.LoopPrespectrum
universe u
namespace QuillenTest.GlobalSectionTelescope

example {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b) :
    (globalTelescope P).map g ≫ (telescopeRestriction P).app b =
      (telescopeRestriction P).app a ≫
        (boundedFlatCoefficientAmbientBassTelescopeFunctor P).map g :=
  (telescopeRestriction P).naturality g

/-- The concrete map into the existing fine telescope is stable at every coefficient. -/
theorem original_telescope_stable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) :
    IsStableEquivalence ((telescopeRestriction P).app a) :=
  telescopeRestriction_isStableEquivalence P a

end QuillenTest.GlobalSectionTelescope
