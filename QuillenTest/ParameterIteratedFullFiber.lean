/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullFiber

/-! # The actual integral base-point original seed-iterate full-open fiber lift -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
    [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

example : IsStableEquivalence
    (iteratedLift f.left (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) :=
  iteratedLift_spec_isStableEquivalence f (Under.mk (𝟙 (CommRingCat.of (ULift.{u} ℤ))))

example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map
    (iteratedLift f.left (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))) :=
  iteratedLift_spec_isStableEquivalence f (Under.mk (𝟙 (CommRingCat.of (ULift.{u} ℤ)))) d

example :
    iteratedLift f.left (op (Spec (CommRingCat.of (ULift.{u} ℤ)))) ≫
        homotopyFiberProjection ((iteratedOpen f.left).app
          (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) =
      (iteratedForget f.left).app (op (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  homotopyFiberLift_projection _ _ _

#print axioms iteratedOpen_fine_square
#print axioms iteratedLift_spec_isStableEquivalence
