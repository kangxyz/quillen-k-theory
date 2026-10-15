/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueTensorDiagonalAdditivity
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SecondEndpointSpan

/-! # Actual Gamma of the original second model weak span -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
open FlasqueTensorAdditivity

def secondGammaSource (R : CommRingCat.{u}) := SecondEndpoint.source R ⋙ Gamma R

def secondGammaCenter (R : CommRingCat.{u}) := SecondEndpoint.center R ⋙ Gamma R

/-- The literal original alpha/Q/beta chain is acted on by the actual exact Gamma. -/
def secondGammaLeftMap (R : CommRingCat.{u}) : secondGammaSource R ⟶ secondGammaCenter R :=
  Functor.whiskerRight (SecondEndpoint.spanLeftMap R) (Gamma R)

/-- The literal original coefficient-resolution and V-unit chain is acted on by actual Gamma. -/
def secondGammaRightMap (R : CommRingCat.{u}) :
    tensorVertex R .second ⟶ secondGammaCenter R :=
  Functor.whiskerRight (SecondEndpoint.spanRightMap R) (Gamma R)

lemma secondGammaSource_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (secondGammaSource R) :=
  (SecondEndpoint.source_exact R).comp (Gamma_exact R)

lemma secondGammaCenter_exact (R : CommRingCat.{u}) : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (secondGammaCenter R) :=
  (SecondEndpoint.center_exact R).comp (Gamma_exact R)

lemma secondGammaLeftMap_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((secondGammaLeftMap R).app K) :=
  (Gamma_exact R).weak ((SecondEndpoint.spanLeftMap R).app K)
    (SecondEndpoint.spanLeftMap_weak R K)

lemma secondGammaRightMap_weak (R : CommRingCat.{u})
    (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((secondGammaRightMap R).app K) :=
  (Gamma_exact R).weak ((SecondEndpoint.spanRightMap R).app K)
    (SecondEndpoint.spanRightMap_weak R K)

/-- Native chosen-zero equality follows from both actual Gamma-mapped weak legs, every n. -/
lemma gammaSecond_KMap_eq_source (R : CommRingCat.{u}) (n : ℕ) :
    tensorVertexKMap R .second n = Waldhausen.KMap (secondGammaSource_exact R) n := by
  have he := Waldhausen.KMap_eq_of_weakNatTrans (tensorVertex_exact R .second)
    (secondGammaCenter_exact R) (secondGammaRightMap R) (secondGammaRightMap_weak R) n
  have hs := Waldhausen.KMap_eq_of_weakNatTrans (secondGammaSource_exact R)
    (secondGammaCenter_exact R) (secondGammaLeftMap R) (secondGammaLeftMap_weak R) n
  exact he.trans hs.symm

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
