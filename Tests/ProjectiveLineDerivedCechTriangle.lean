/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DerivedCechTriangle

/-!
# Original-map consumers of the relative projective-line derived Čech triangle

The vertices, signed differential, connecting arrow, and acyclic comparison
naturality use the genuine original module-sheaf and derived functors.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Quillen.Scheme.ProjectiveLine Quillen.Scheme.PolynomialLaurent Quillen.SchemeSheaf

namespace Quillen.Tests.ProjectiveLineDerivedCechTriangle

/-- Use the standard derived category of the original module sheaves. -/
local instance derivedCechTestsStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) [M.IsQuasicoherent]

/-- The first vertex is the original relative module-sheaf derived image. -/
theorem original_derived_vertex :
    (derivedCechTriangle R M).obj₁ =
      (derivedPushforwardPlus (projection R)).obj
        ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M) := rfl

/-- The second vertex is the ordinary direct image of the actual chart pair. -/
theorem original_chart_pair_vertex :
    (derivedCechTriangle R M).obj₂ =
      (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
        ((Scheme.Modules.pushforward (projection R)).obj
          ((openLocalization (plusChart R)).obj M ⨯
            (openLocalization (minusChart R)).obj M)) := rfl

/-- The differential retains both original restrictions and their plus-minus order. -/
theorem original_signed_differential :
    (derivedCechTriangle R M).mor₂ =
      (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).map
        ((Scheme.Modules.pushforward (projection R)).map
          (prod.fst ≫ openLocalizationMap (laurentPlus R) (plusChart R) M -
            prod.snd ≫ TwoOpen.sheafSecondRestriction (laurentPlus R) (laurentMinus R)
              (plusChart R) (minusChart R) (overlap_equation R) M)) := rfl

/-- The overlap vertex uses the literal original composite immersion. -/
theorem original_overlap_vertex :
    (derivedCechTriangle R M).obj₃ =
      (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
        ((Scheme.Modules.pushforward (projection R)).obj
          ((openLocalization (laurentPlus R ≫ plusChart R)).obj M)) := rfl

/-- The connecting arrow is retained through the installed original overlap-unit comparison. -/
theorem original_connecting_arrow :
    letI : IsIso ((derivedPushforwardPlusUnit (projection R)).app
        (singleZeroPlus (twoChartLine R)
          ((openLocalization (laurentPlus R ≫ plusChart R)).obj M))) :=
      TwoOpen.isIso_sheafSequence_third_derivedUnit
      (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R)
      (overlap_equation R) (projection R) M
    (derivedCechTriangle R M).mor₃ =
      (derivedPushforwardPlusSingleIso (projection R)
        ((openLocalization (laurentPlus R ≫ plusChart R)).obj M)).inv ≫
        ((derivedPushforwardPlus (projection R)).mapTriangle.obj
          (TwoOpen.sheafSequence_shortExact (laurentPlus R) (laurentMinus R)
            (plusChart R) (minusChart R) (chart_isPullback R) M
            (charts_jointly_surjective R)).singleTrianglePlus).mor₃ := rfl

/-- The original acyclic comparison preserves an arbitrary sheaf arrow. -/
theorem original_single_comparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : X.Modules} (φ : A ⟶ B)
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X A))]
    [IsIso ((derivedPushforwardPlusUnit f).app (singleZeroPlus X B))] :
    (derivedPushforwardPlus f).map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ) ≫
        (derivedPushforwardPlusSingleIso f B).hom =
      (derivedPushforwardPlusSingleIso f A).hom ≫
        (DerivedCategory.Plus.singleFunctor Y.Modules 0).map
          ((Scheme.Modules.pushforward f).map φ) :=
  derivedPushforwardPlusSingleIso_naturality f φ

/-- The actual positive-chart acyclic comparison retains the installed projection unit. -/
theorem original_positive_unit_square
    (A : (Spec (.of (Polynomial R))).Modules) [A.IsQuasicoherent] :
    letI := isIso_derivedPushforwardPlusUnit_pushforward_single (plusChart R) (projection R) A
    (derivedPushforwardPlusUnit (projection R)).app
        (singleZeroPlus (twoChartLine R) ((Scheme.Modules.pushforward (plusChart R)).obj A)) ≫
        (derivedPushforwardPlusSingleIso (projection R)
          ((Scheme.Modules.pushforward (plusChart R)).obj A)).hom =
      DerivedCategory.Plus.Q.map
        (pushforwardSingleZeroPlusIso (projection R)
          ((Scheme.Modules.pushforward (plusChart R)).obj A)).hom := by
  let := isIso_derivedPushforwardPlusUnit_pushforward_single (plusChart R) (projection R) A
  exact derivedPushforwardPlusSingleIso_unit _ _

/-- The actual relative computation includes nonreduced base rings. -/
theorem nonreduced_distinguished
    (N : (twoChartLine (.of (ZMod 4))).Modules) [N.IsQuasicoherent] :
    derivedCechTriangle (.of (ZMod 4)) N ∈
      distTriang (DerivedCategory.Plus (Spec (.of (ZMod 4))).Modules) :=
  derivedCechTriangle_distinguished _ N

/-- The actual relative computation includes the zero ring. -/
theorem zero_ring_distinguished
    (N : (twoChartLine (.of (ZMod 1))).Modules) [N.IsQuasicoherent] :
    derivedCechTriangle (.of (ZMod 1)) N ∈
      distTriang (DerivedCategory.Plus (Spec (.of (ZMod 1))).Modules) :=
  derivedCechTriangle_distinguished _ N

end Quillen.Tests.ProjectiveLineDerivedCechTriangle
