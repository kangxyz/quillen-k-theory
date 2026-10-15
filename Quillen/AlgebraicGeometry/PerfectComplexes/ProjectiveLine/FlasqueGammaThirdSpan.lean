/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTensorDiagonalAdditivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueThirdSpan
public import Quillen.Waldhausen.Functoriality.KMap

/-! # Gamma of the actual original third model weak span -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTensorAdditivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
open FlasqueTensorAdditivity

/-- The actual original center, followed by actual Gamma. -/
def thirdGammaCenter (R : CommRingCat.{u}) := FlasqueThirdEndpoint.center R ⋙ Gamma R

/-- The actual total of K RIGHT tensor Q, followed by actual Gamma. -/
def rightQTotalGamma (R : CommRingCat.{u}) := FlasqueThirdEndpoint.rightQTotal R ⋙ Gamma R

/-- Actual Gamma of the actual original installed section-unit first leg. -/
def thirdGammaToCenter (R : CommRingCat.{u}) :
    tensorVertex R .third ⟶ thirdGammaCenter R :=
  Functor.whiskerRight (FlasqueThirdEndpoint.thirdToCenter R) (Gamma R)

/-- Actual Gamma of the actual original right-Q-total section-unit second leg. -/
def rightQTotalGammaToCenter (R : CommRingCat.{u}) :
    rightQTotalGamma R ⟶ thirdGammaCenter R :=
  Functor.whiskerRight (FlasqueThirdEndpoint.totalToCenter R) (Gamma R)

lemma thirdGammaCenter_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (thirdGammaCenter R) :=
  (FlasqueThirdEndpoint.center_exact R).comp (Gamma_exact R)

lemma rightQTotalGamma_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (rightQTotalGamma R) :=
  (FlasqueThirdEndpoint.rightQTotal_exact R).comp (Gamma_exact R)

/-- Actual Gamma preserves weakness of the original first model leg. -/
lemma thirdGammaToCenter_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((thirdGammaToCenter R).app K) :=
  (Gamma_exact R).weak ((FlasqueThirdEndpoint.thirdToCenter R).app K)
    (FlasqueThirdEndpoint.thirdToCenter_weak R K)

/-- Actual Gamma preserves weakness of the original second model leg. -/
lemma rightQTotalGammaToCenter_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
      ((rightQTotalGammaToCenter R).app K) :=
  (Gamma_exact R).weak ((FlasqueThirdEndpoint.totalToCenter R).app K)
    (FlasqueThirdEndpoint.totalToCenter_weak R K)

/-- The mapped first chain arrow retains its original section-unit data and actual LEFT order. -/
lemma thirdGammaToCenter_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((thirdGammaToCenter R).app K).hom = (godementTotal (twoChartLine R)).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map
        ((FlasqueThirdEndpoint.thirdToCenter R).app K).hom) :=
  Gamma_map R ((FlasqueThirdEndpoint.thirdToCenter R).app K)

/-- The mapped second chain arrow retains its original section-unit data and actual LEFT order. -/
lemma rightQTotalGammaToCenter_hom_app (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((rightQTotalGammaToCenter R).app K).hom = (godementTotal (twoChartLine R)).map
      ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map
        ((FlasqueThirdEndpoint.totalToCenter R).app K).hom) :=
  Gamma_map R ((FlasqueThirdEndpoint.totalToCenter R).app K)

/-- The actual Gamma-third vertex and Gamma-right-Q-total have identical native K-maps. -/
lemma gammaThird_KMap_eq_rightQTotal (R : CommRingCat.{u}) (n : ℕ) :
    tensorVertexKMap R .third n = Waldhausen.KMap (rightQTotalGamma_exact R) n := by
  have he := Waldhausen.KMap_eq_of_weakNatTrans (tensorVertex_exact R .third)
    (thirdGammaCenter_exact R) (thirdGammaToCenter R) (thirdGammaToCenter_weak R) n
  have hq := Waldhausen.KMap_eq_of_weakNatTrans (rightQTotalGamma_exact R)
    (thirdGammaCenter_exact R) (rightQTotalGammaToCenter R)
    (rightQTotalGammaToCenter_weak R) n
  exact he.trans hq.symm

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
