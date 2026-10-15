/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FiniteFlatPushforwardNaturality

/-! An independent client of the original finite flat Kvb-to-strict comparison. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Consumer.StrictFiniteFlatPushforward

/-- The public degree-zero comparison commutes with the actual direct images. -/
theorem original_degree_zero {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]
    (x : AlgebraicGeometry.Scheme.Modules.SchemeK Z 0) :
    strictKFiniteFlatPushforward f 0 (vectorBundleToStrictKMap Z 0 x) =
      vectorBundleToStrictKMap X 0 (AlgebraicGeometry.Scheme.Modules.schemeKPushforward f 0 x) :=
  DFunLike.congr_fun (vectorBundleToStrictKMap_finiteFlatPushforward f 0) x

end Consumer.StrictFiniteFlatPushforward
