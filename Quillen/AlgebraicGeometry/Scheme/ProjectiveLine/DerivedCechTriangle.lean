/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenDerivedTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness

/-!
# Relative derived Čech computation on the genuine two-chart projective line

For every quasicoherent module sheaf over an arbitrary commutative base ring,
the original projection direct image is the first vertex of the actual signed
two-chart triangle. All affine acyclicity conditions are discharged. The
comparison retains the original derived short-exact triangle; no flat
coefficient-base-change or projective-bundle generation assertion is made.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry
namespace Quillen.Scheme.ProjectiveLine
open Quillen.Scheme.PolynomialLaurent Quillen.SchemeSheaf
/-- Use the standard derived category of actual module sheaves. -/
local instance projectiveDerivedCechStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) [M.IsQuasicoherent]
/-- Actual relative direct image is computed by the genuine signed two-chart triangle. -/
def derivedCechTriangle : Triangle (DerivedCategory.Plus (Spec R).Modules) :=
  TwoOpen.sheafDerivedCechTriangle (laurentPlus R) (laurentMinus R)
    (plusChart R) (minusChart R) (chart_isPullback R) (charts_jointly_surjective R) (projection R) M
/-- The comparison retains the actual derived short-exact triangle of the chart cover. -/
def derivedCechTriangleIso :
    derivedCechTriangle R M ≅
      (derivedPushforwardPlus (projection R)).mapTriangle.obj
        (TwoOpen.sheafSequence_shortExact (laurentPlus R) (laurentMinus R)
          (plusChart R) (minusChart R) (chart_isPullback R) M
          (charts_jointly_surjective R)).singleTrianglePlus :=
  TwoOpen.sheafDerivedCechTriangleIso (laurentPlus R) (laurentMinus R)
    (plusChart R) (minusChart R) (chart_isPullback R) (charts_jointly_surjective R) (projection R) M
/-- The first vertex is the original module-sheaf derived direct image, over the original base. -/
theorem derivedCechTriangle_obj₁ :
    (derivedCechTriangle R M).obj₁ =
      (derivedPushforwardPlus (projection R)).obj
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M) := rfl
/-- The actual relative Čech differential preserves its original sign and restriction maps. -/
theorem derivedCechTriangle_mor₂ :
    (derivedCechTriangle R M).mor₂ =
      (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).map
        ((Scheme.Modules.pushforward (projection R)).map
          (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
            (plusChart R) (minusChart R) (overlap_equation R) M)) := rfl
/-- The actual projective-line derived Čech triangle is distinguished over arbitrary base rings. -/
theorem derivedCechTriangle_distinguished :
    derivedCechTriangle R M ∈ distTriang (DerivedCategory.Plus (Spec R).Modules) :=
  TwoOpen.sheafDerivedCechTriangle_distinguished (laurentPlus R) (laurentMinus R)
    (plusChart R) (minusChart R) (chart_isPullback R) (charts_jointly_surjective R) (projection R) M
end Quillen.Scheme.ProjectiveLine
end
