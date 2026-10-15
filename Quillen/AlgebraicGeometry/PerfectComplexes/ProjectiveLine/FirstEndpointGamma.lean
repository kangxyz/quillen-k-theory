/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FirstEndpointNegativeSpan
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTensorDiagonalSequence
public import Quillen.Waldhausen.Functoriality.KMap

/-! # Original Gamma first endpoint and the actual all-degree K-map weak-span law -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
variable (R : CommRingCat.{u})

/-- Only native associations identify the explicit right endpoint with ORIGINAL Gamma(Efirst). -/
def gammaFirstIso : negativeSpanRight R ≅ FlasqueTensorAdditivity.tensorVertex R .first :=
  let E := originalFirst R
  let I := FlasqueBoundedBelow.inclusion (twoChartLine R)
  let L := FlasqueTwoSummands.boundedNegativeTwist R
  let T := FlasqueBoundedBelow.total (twoChartLine R)
  Functor.associator E I (L ⋙ T) ≪≫
    Functor.isoWhiskerLeft E (Functor.associator I L T).symm

/-- The actual beta under LEFT line tensor and T, retaining the original Gamma association. -/
def gammaFirstMap : FlasqueTensorAdditivity.tensorVertex R .first ⟶ negativeSpanCenter R :=
  (gammaFirstIso R).inv ≫ negativeSpanRightMap R

lemma gammaFirstMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (gammaFirstMap R).app K = (gammaFirstIso R).inv.app K ≫
      (negativeTotal R).map ((betaBounded R).app K) := rfl

lemma gammaFirstMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((gammaFirstMap R).app K) := by
  change (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    ((gammaFirstIso R).inv.app K ≫ (negativeSpanRightMap R).app K)
  exact (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq.comp_mem _ _
    ((FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq_iso _ inferInstance)
    (negativeSpanRightMap_weak R K)

/-- ORIGINAL native negative coefficient and ORIGINAL Gamma first vertex induce the same K-map. -/
theorem negativeColumn_KMap_eq_gammaFirst (n : ℕ) :
    Waldhausen.KMap (negativeSpanLeft_exact R) n =
      Waldhausen.KMap (FlasqueTensorAdditivity.tensorVertex_exact R .first) n :=
  (Waldhausen.KMap_eq_of_weakNatTrans (negativeSpanLeft_exact R)
    (negativeSpanCenter_exact R) (negativeSpanLeftMap R) (negativeSpanLeftMap_weak R) n).trans
      (Waldhausen.KMap_eq_of_weakNatTrans
        (FlasqueTensorAdditivity.tensorVertex_exact R .first) (negativeSpanCenter_exact R)
        (gammaFirstMap R) (gammaFirstMap_weak R) n).symm

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
