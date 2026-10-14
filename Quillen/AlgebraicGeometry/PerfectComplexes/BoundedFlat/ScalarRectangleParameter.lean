/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Path.HomotopyThreeRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareScalarPaths

/-! The complete scalar parameter word in the actual common seventeen-simplex. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Quillen.SimplexParameters
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths

/-- Exact scalar counterpart of the original `boundedFlatDoubleSquareTrackComparison` word. -/
def rectangleParameter :
    ((firstRestriction.symm.trans secondRestriction).trans
      (middleChart.symm.trans lastRestriction)).Homotopy
    (sourceChart.symm.trans ((sourceTotal.symm.trans targetTotal).trans targetChart)) :=
  Path.Homotopy.threeRoutes firstComparison middleComparison lastComparison

end Quillen.PerfectComplexes.DoubleSquareScalarPaths
