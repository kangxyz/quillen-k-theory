/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPushforwardComparison

/-! The original finite-flat comparison identifies maps into strict derived direct image. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
namespace Consumer.DerivedPushforwardComparison
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

lemma original_unit_detects_maps {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsFinite f] [Flat f] [IsLocallyNoetherian X]
    (K : AlgebraicGeometry.Scheme.Modules.Complex.StrictPerfect Z)
    {T : DerivedCategory.Plus X.Modules}
    (p q : T ⟶ (strictToDerivedPlus X).obj ((strictFiniteFlatPushforward f).obj K)) :
    p ≫ (derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj K) =
      q ≫ (derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj K) ↔ p = q := by
  have : IsIso ((derivedPushforwardPlusUnit f).app ((strictToPlus Z).obj K)) :=
    isIso_derivedPushforwardPlusUnit_strict f K
  exact cancel_mono _

end Consumer.DerivedPushforwardComparison
