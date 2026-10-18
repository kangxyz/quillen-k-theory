/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionFullOpenFiber

/-! Regression for the actual support-forgetful coordinate of the stable fiber lift. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open FullOpenTelescope
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

example (a : Under R) :
    fiberMap f a ≫ homotopyFiberProjection ((openMap f).app a) =
      (LocalizationTelescope.forget f).app a :=
  homotopyFiberLift_projection ((openMap f).app a) ((LocalizationTelescope.forget f).app a)
    ((null f).homotopy a)
