/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedPushforward

/-! An independent consumer of the original affine derived comparison unit. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Consumer.AffineDerivedPushforward
/-- The standard actual derived category of scheme module sheaves. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The actual comparison unit detects equality of incoming bounded-below derived arrows. -/
theorem original_unit_detects_maps {Z X : Scheme.{u}} (f : Z ⟶ X) [IsAffineHom f]
    (M : Z.Modules) [M.IsQuasicoherent] {T : DerivedCategory.Plus X.Modules}
    (a b : T ⟶
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj
        (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M))
    (h : a ≫ (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app
        (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M) =
      b ≫ (AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app
        (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M)) : a = b := by
  let := AlgebraicGeometry.Scheme.Modules.isIso_derivedPushforwardPlusUnit_single f M
  exact (cancel_mono ((AlgebraicGeometry.Scheme.Modules.derivedPushforwardPlusUnit f).app
    (AlgebraicGeometry.Scheme.Modules.singleZeroPlus Z M))).mp h

end Consumer.AffineDerivedPushforward
