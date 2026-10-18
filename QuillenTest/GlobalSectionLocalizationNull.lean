/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLocalizationNull

/-! Regression for strict coefficient naturality of the actual original null. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

example {a b : Under R} (g : a ⟶ b) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((openRow f).map g)).map n
        (((globalSupportedOpenNull f).homotopy a).level n (s, x)) =
      ((globalSupportedOpenNull f).homotopy b).level n
        (s, (prespectrumMap ((supportedRow f).map g)).map n x) :=
  (globalSupportedOpenNull f).naturality g n s x
