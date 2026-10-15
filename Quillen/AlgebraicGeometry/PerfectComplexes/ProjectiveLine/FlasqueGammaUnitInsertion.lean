/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueNegativeGamma
public import Quillen.Waldhausen.Functoriality.KMap

/-! # The actual model left-tensor insertion of the original Godement unit -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
open FlasqueTensorAdditivity

/-- Actual original LEFT negative-line tensor followed by actual totalization. -/
def negativeTotal (R : CommRingCat.{u}) :
    BoundedBelow.Obj (twoChartLine R) ⥤ FlasqueBoundedBelow.Obj (twoChartLine R) :=
  FlasqueTwoSummands.boundedNegativeTwist R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

/-- The actual original model unit, mapped by the actual LEFT negative-line tensor. -/
def negativeInsertionBounded (R : CommRingCat.{u}) :
    FlasqueTwoSummands.boundedNegativeTwist R ⟶
      FlasqueBoundedBelow.total (twoChartLine R) ⋙ leftNegative R where
  app K := (FlasqueTwoSummands.boundedNegativeTwist R).map
    ((FlasqueBoundedBelow.unit (twoChartLine R)).app K)
  naturality {K L} f := by
    change (FlasqueTwoSummands.boundedNegativeTwist R).map f ≫
      (FlasqueTwoSummands.boundedNegativeTwist R).map
        ((FlasqueBoundedBelow.unit (twoChartLine R)).app L) =
      (FlasqueTwoSummands.boundedNegativeTwist R).map
        ((FlasqueBoundedBelow.unit (twoChartLine R)).app K) ≫
      (FlasqueTwoSummands.boundedNegativeTwist R).map
        ((FlasqueBoundedBelow.total (twoChartLine R) ⋙
          FlasqueBoundedBelow.inclusion (twoChartLine R)).map f)
    rw [← (FlasqueTwoSummands.boundedNegativeTwist R).map_comp,
      ← (FlasqueTwoSummands.boundedNegativeTwist R).map_comp]
    exact congrArg (FlasqueTwoSummands.boundedNegativeTwist R).map
      ((FlasqueBoundedBelow.unit (twoChartLine R)).naturality f)

/-- The actual natural map T(L LEFT tensor C) to T(L LEFT tensor T(C)). -/
def negativeInsertion (R : CommRingCat.{u}) :
    negativeTotal R ⟶ FlasqueBoundedBelow.total (twoChartLine R) ⋙ Gamma R where
  app K := (FlasqueBoundedBelow.total (twoChartLine R)).map
    ((negativeInsertionBounded R).app K)
  naturality {K L} f := by
    change (FlasqueBoundedBelow.total (twoChartLine R)).map
        ((FlasqueTwoSummands.boundedNegativeTwist R).map f) ≫
      (FlasqueBoundedBelow.total (twoChartLine R)).map
        ((negativeInsertionBounded R).app L) =
      (FlasqueBoundedBelow.total (twoChartLine R)).map
        ((negativeInsertionBounded R).app K) ≫
      (FlasqueBoundedBelow.total (twoChartLine R)).map
        ((FlasqueBoundedBelow.total (twoChartLine R) ⋙ leftNegative R).map f)
    rw [← (FlasqueBoundedBelow.total (twoChartLine R)).map_comp,
      ← (FlasqueBoundedBelow.total (twoChartLine R)).map_comp]
    exact congrArg (FlasqueBoundedBelow.total (twoChartLine R)).map
      ((negativeInsertionBounded R).naturality f)

/-- Before total, the actual insertion is the original LEFT tensor of the original model unit. -/
lemma negativeInsertionBounded_hom_app (R : CommRingCat.{u})
    (K : BoundedBelow.Obj (twoChartLine R)) :
    ((negativeInsertionBounded R).app K).hom =
      (tensorByLineComplex (tautologicalLine R)).map
        ((FlasqueBoundedBelow.unit (twoChartLine R)).app K).hom := rfl

/-- Totalization retains the actual original bounded insertion chain map. -/
lemma negativeInsertion_hom_app (R : CommRingCat.{u})
    (K : BoundedBelow.Obj (twoChartLine R)) :
    ((negativeInsertion R).app K).hom = (godementTotal (twoChartLine R)).map
      ((negativeInsertionBounded R).app K).hom := rfl

/-- Original weak units remain weak after the proved exact line and total functors. -/
lemma negativeInsertion_weak (R : CommRingCat.{u})
    (K : BoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((negativeInsertion R).app K) :=
  FlasqueBoundedBelow.total_weak ((negativeInsertionBounded R).app K)
    ((FlasqueTwoSummands.boundedNegativeTwist_exact R).weak
      ((FlasqueBoundedBelow.unit (twoChartLine R)).app K)
      (FlasqueBoundedBelow.unit_weak (twoChartLine R) K))

lemma negativeTotal_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen (twoChartLine R)).cof
    (BoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (negativeTotal R) :=
  (FlasqueTwoSummands.boundedNegativeTwist_exact R).comp
    (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- Actual chosen-zero K-maps of the original unit insertion agree in every degree. -/
lemma negativeInsertion_KMap (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap (negativeTotal_exact R) n =
      Waldhausen.KMap ((FlasqueBoundedBelow.total_exact (twoChartLine R)).comp
        (Gamma_exact R)) n :=
  Waldhausen.KMap_eq_of_weakNatTrans (negativeTotal_exact R)
    ((FlasqueBoundedBelow.total_exact (twoChartLine R)).comp (Gamma_exact R))
    (negativeInsertion R) (negativeInsertion_weak R) n

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
