/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.ChartAffineness
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineCompositeDerivedPushforward

/-! # Actual acyclic chart terms for the original projective-line projection -/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf

namespace Quillen.Tests.ProjectiveLineChartAcyclicity

/-- Use the installed standard derived category of original module sheaves. -/
local instance chartAcyclicityDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- The installed projection unit is invertible on the actual positive chart direct image. -/
theorem original_positive_chart_unit (R : CommRingCat.{u})
    (M : (Spec (.of (Polynomial R))).Modules) [M.IsQuasicoherent] :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) ((Scheme.Modules.pushforward (plusChart R)).obj M))) :=
  isIso_derivedPushforwardPlusUnit_pushforward_single (plusChart R) (projection R) M

/-- The installed projection unit is invertible on the actual negative chart direct image. -/
theorem original_negative_chart_unit (R : CommRingCat.{u})
    (M : (Spec (.of (Polynomial R))).Modules) [M.IsQuasicoherent] :
    IsIso ((derivedPushforwardPlusUnit (projection R)).app
      (singleZeroPlus (twoChartLine R) ((Scheme.Modules.pushforward (minusChart R)).obj M))) :=
  isIso_derivedPushforwardPlusUnit_pushforward_single (minusChart R) (projection R) M

end Quillen.Tests.ProjectiveLineChartAcyclicity
