/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftTerminalNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftTerminalUnit

/-! The exact terminal first-old seed equals the entire C1 endpoint in the common carrier. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalSeed
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftTerminalNull
open CoefficientBassPositiveLeftTerminalUnit
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original inverse-null, original V_p, forward-null word, between the two distinct tips. -/
def terminalSeed : Path (minusTip P p q) (plusTip P p q) :=
  (oldNull P p q false).symm.trans
    ((firstOldUnit P p q).trans (oldNull P p q true))

/-- The whole C1 endpoint is used with its actual values and unchanged path coordinate. -/
def endpoint : Path (minusTip P p q) (plusTip P p q) where
  toFun s := CoefficientBassPositiveC1SeedFace.face P p q (1, s)
  continuous_toFun := by fun_prop
  source' := CoefficientBassPositiveC1SeedFace.face_bottom P p q 1
  target' := CoefficientBassPositiveC1SeedFace.face_top P p q 1

/-- The entire terminal seed equality follows from its three proved whole carrier pieces. -/
theorem terminal_parameter (s : I) : terminalSeed P p q s =
    CoefficientBassPositiveC1SeedFace.face P p q (1, s) := by
  change ((oldNull P p q false).symm.trans
    ((firstOldUnit P p q).trans (oldNull P p q true))) s =
      ((CoefficientBassPositiveC1SeedFace.nullMinus P p q).symm.trans
        ((CoefficientBassPositiveC1SeedFace.forwardUnit P p q).trans
          (CoefficientBassPositiveC1SeedFace.nullPlus P p q))) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ordinary_null P p q (unitInterval.symm _)
  · rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact terminal_carrier P p q _
    · exact shifted_null P p q _

/-- Equality of complete typed paths, preserving all nine nested outer blocks and their clocks. -/
theorem terminalSeed_eq_endpoint : terminalSeed P p q = endpoint P p q := by
  ext s
  exact terminal_parameter P p q s

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalSeed
