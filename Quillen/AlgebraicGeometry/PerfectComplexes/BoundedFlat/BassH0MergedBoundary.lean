/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0MergedNative

/-! All five shared scalar edges of the four whole original faces in the actual common family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Merged

/-- The exact positive H0/chart edge retains every original segment and speed. -/
theorem h0_plus_scalar (s : unitInterval) :
    BassSupportOrder.h0Parameter (s, 0) = BassSupportOrder.plusParameter (0, s) :=
  BassSupportOrder.h0_plus_scalar s

/-- The separate inverse H0/chart edge retains its original parameterization. -/
theorem h0_minus_scalar (s : unitInterval) :
    BassSupportOrder.h0Parameter (s, 1) = BassSupportOrder.minusParameter (0, s) :=
  BassSupportOrder.h0_minus_scalar s

/-- The source H0/bottom edge retains the actual realization-product column path. -/
theorem h0_bottom_scalar (t : unitInterval) :
    BassSupportOrder.h0Parameter (0, t) = BassSupportOrder.bottomParameter.{u} (0, t) :=
  BassSupportOrder.h0_bottom_scalar t

/-- The earlier positive chart/bottom scalar identity survives unchanged in the joint family. -/
theorem plus_bottom_scalar (r : unitInterval) :
    BassSupportOrder.plusParameter (r, 0) = BassSupportOrder.bottomParameter.{u} (r, 0) :=
  congrArg (StdSimplex.map BassSupportOrder.oldIndex) (BassReferenceMerge.plus_bottom_scalar r)

/-- The earlier inverse chart/bottom scalar identity survives in the same actual family. -/
theorem minus_bottom_scalar (r : unitInterval) :
    BassSupportOrder.minusParameter (r, 0) = BassSupportOrder.bottomParameter.{u} (r, 1) :=
  congrArg (StdSimplex.map BassSupportOrder.oldIndex) (BassReferenceMerge.minus_bottom_scalar r)

end Quillen.PerfectComplexes.BassH0Merged
