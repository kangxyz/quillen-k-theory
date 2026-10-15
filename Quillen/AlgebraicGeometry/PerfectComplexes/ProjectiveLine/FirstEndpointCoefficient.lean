/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueCoefficientOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SelfBaseChangeSpan
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalGenerationUnitEquations

/-!
# The actual original first coefficient augmentation

The prescribed right tensor K tensor L is totalized on P. Its original
augmentation is pulled along p1 and compared with the literal original F1(K)
using the original tautological pullback-tensor mate, in its original order.
No flasqueness of K tensor L is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Godement

open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
open FlasqueCoefficients
variable (R : CommRingCat.{u})
local instance firstFlat : Flat (relativeFirst R) := by
  dsimp [relativeFirst]
  infer_instance

/-- The literal original right coefficient C = K tensor L. -/
abbrev coefficientPlus := rightTensorPlus R

/-- The literal original resolved coefficient M = T_P(C). -/
abbrev resolved := rightTensorTotal R

/-- The original installed coefficient augmentation, preserving its actual chain maps. -/
abbrev coefficientUnit := tensorTotalUnit R

lemma coefficientUnit_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((coefficientUnit R).app K).hom =
      (godementTotalUnit (twoChartLine R)).app
        ((AlgebraicGeometry.Scheme.Modules.Complex.tensorRight (tautologicalLine R)).obj K.obj) :=
          rfl

lemma coefficientUnit_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((coefficientUnit R).app K).hom :=
  tensorTotalUnit_quasiIso R K

/-- The actual first pullback of the prescribed right tensor. -/
def pulledCoefficientPlus :=
  coefficientPlus R ⋙ (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus

/-- The literal original incidence first coefficient F1(K). -/
def originalFirstPlus :=
  toPlus (twoChartLine R) ⋙ (FlasqueDiagonal.coefficient R .first).mapCochainComplexPlus

/-- The original pullback-tensor mate, with its original forward orientation. -/
def coefficientPullbackIso : pulledCoefficientPlus R ≅ originalFirstPlus R :=
  NatIso.ofComponents (fun K =>
    ((Functor.mapCochainComplexPlusCompIso
      (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R))
      (Scheme.Modules.pullback (relativeFirst R))).symm ≪≫
        NatIso.mapCochainComplexPlus
          (tautologicalPullbackTensorNatIso R (relativeFirst R))).app
            ((toPlus (twoChartLine R)).obj K))
    (fun f => by
      exact (((Functor.mapCochainComplexPlusCompIso
        (moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R))
        (Scheme.Modules.pullback (relativeFirst R))).symm ≪≫
          NatIso.mapCochainComplexPlus
            (tautologicalPullbackTensorNatIso R (relativeFirst R))).hom.naturality
              ((toPlus (twoChartLine R)).map f)))

/-- The original first pullback of the actual resolved coefficient. -/
def pulledResolvedPlus :=
  (resolved R ⋙ toPlus (twoChartLine R)) ⋙
    (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus

/-- F1(K) first uses the INVERSE original coefficient iso, then the original pulled unit. -/
def coefficientMap : originalFirstPlus R ⟶ pulledResolvedPlus R :=
  (coefficientPullbackIso R).inv ≫
    CategoryTheory.Functor.whiskerRight (coefficientUnit R)
      (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus

lemma coefficientMap_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (coefficientMap R).app K =
      (coefficientPullbackIso R).inv.app K ≫
        (Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus.map
          ((coefficientUnit R).app K) := rfl

/-- The original pulled coefficient map is genuinely weak before either pushforward. -/
lemma coefficientMap_quasiIso (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    QuasiIso ((coefficientMap R).app K).hom := by
  have : QuasiIso ((coefficientUnit R).app K).hom := coefficientUnit_quasiIso R K
  have : QuasiIso
      ((Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus.map
        ((coefficientUnit R).app K)).hom :=
    AlgebraicGeometry.Scheme.Modules.Complex.pullback_quasiIso (relativeFirst R) ((coefficientUnit
      R).app K).hom
  have : QuasiIso ((coefficientPullbackIso R).inv.app K).hom := inferInstance
  change QuasiIso (((coefficientPullbackIso R).inv.app K).hom ≫
    ((Scheme.Modules.pullback (relativeFirst R)).mapCochainComplexPlus.map
      ((coefficientUnit R).app K)).hom)
  infer_instance

end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
