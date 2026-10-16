/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FiniteFlatPushforwardNaturality

/-! Consumers of actual strict-perfect finite flat direct image and its K-comparison. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace QuillenTest.StrictFiniteFlatPushforward

open Quillen
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

omit [IsLocallyNoetherian Z] in
/-- The complex map retains the original direct image in every degree. -/
theorem original_component {K L : StrictPerfect Z} (s : K ⟶ L) (i : ℤ) :
    ((strictFiniteFlatPushforward f).map s).hom.f i =
      (Scheme.Modules.pushforward f).map (s.hom.f i) := rfl

/-- Every original quasi-isomorphism, without a chosen homotopy inverse, is preserved. -/
theorem original_quasiIso {K L : StrictPerfect Z} (s : K ⟶ L) [QuasiIso s.hom] :
    QuasiIso ((strictFiniteFlatPushforward f).map s).hom :=
  strictFiniteFlatPushforward_quasiIso f s

/-- All inherited conflations are preserved, without choosing global degreewise splittings. -/
theorem original_conflation (S : ShortComplex (StrictPerfect Z))
    (hS : (S.map (strictPerfect Z).ι).ShortExact) :
    ((S.map (strictFiniteFlatPushforward f)).map (strictPerfect X).ι).ShortExact :=
  (strictExactFiniteFlatPushforward f).map_conflation S hS

/-- The original public Kvb-to-strict comparison commutes on each K-class. -/
theorem original_K_comparison (n : ℕ) (x : AlgebraicGeometry.Scheme.Modules.SchemeK Z n) :
    strictKFiniteFlatPushforward f n (vectorBundleToStrictKMap Z n x) =
      vectorBundleToStrictKMap X n (AlgebraicGeometry.Scheme.Modules.schemeKPushforward f n x) :=
  DFunLike.congr_fun (vectorBundleToStrictKMap_finiteFlatPushforward f n) x

end QuillenTest.StrictFiniteFlatPushforward
