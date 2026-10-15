/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTensorDiagonalSequence
public import Quillen.Waldhausen.Additivity.GroupFormula

/-! # Native chosen-zero additivity for the actual left-tensored diagonal sequence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity

/-- The original native K-map of each actual transported diagonal vertex. -/
def tensorVertexKMap (R : CommRingCat.{u}) (v : FlasqueDiagonal.Vertex) (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n →*
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n :=
  Waldhausen.KMap (tensorVertex_exact R v) n

/-- Original subobject-then-quotient multiplication for the actual mapped conflation,
in every native degree, including zero. No derived triangle or inverse premise is used. -/
theorem tensorDiagonal_KMap_additivity (R : CommRingCat.{u}) (n : ℕ)
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    tensorVertexKMap R .second n x =
      tensorVertexKMap R .first n x * tensorVertexKMap R .third n x :=
  Waldhausen.Additivity.KMap_additivity_mul
    (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (tensorIncidence R) (tensorQuotient R) (tensorSequence_isCofibrationSequence R) n x

/-- Native K0 is an actual covered degree of the same literal formula. -/
theorem tensorDiagonal_K0_additivity (R : CommRingCat.{u})
    (x : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K 0) :
    tensorVertexKMap R .second 0 x =
      tensorVertexKMap R .first 0 x * tensorVertexKMap R .third 0 x :=
  tensorDiagonal_KMap_additivity R 0 x

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity
