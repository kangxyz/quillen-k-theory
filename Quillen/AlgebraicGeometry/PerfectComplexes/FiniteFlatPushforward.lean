/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FiniteFlatPushforward


public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Pushforward
public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion
public import Quillen.Waldhausen.ExactFunctor
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.FinitePushforward

/-! # Finite flat direct image of strict perfect complexes

The original termwise direct image preserves bounded finite locally free terms.
Exact coherent direct image proves preservation of actual quasi-isomorphisms,
and exact vector-bundle direct image proves preservation of all inherited
conflations and cofibration pushouts. The degree-zero vector-bundle inclusion
commutes with this actual functor. No direct image of arbitrary locally perfect
representatives is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.PerfectComplexes
variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
  (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] [Flat f]

/-- Actual direct image preserves cofibrations, their pushouts, and quasi-isomorphisms. -/
theorem strictFiniteFlatPushforward_waldhausenExact :
    Waldhausen.IsExact (strictWaldhausen Z).cof (strictWaldhausen Z).weq
      (strictWaldhausen X).cof (strictWaldhausen X).weq (strictFiniteFlatPushforward f) where
  zero h := (strictFiniteFlatPushforward f).map_isZero h
  cofibration s hs := (strictExactFiniteFlatPushforward f).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact strictFiniteFlatPushforward_quasiIso f s
  pushout hi h := (strictExactFiniteFlatPushforward f).waldhausenExact.pushout hi h

/-- The genuine strict-perfect Waldhausen K-map induced by finite flat direct image. -/
def strictKFiniteFlatPushforward (n : ℕ) : StrictK Z n →* StrictK X n :=
  Waldhausen.KMap (strictFiniteFlatPushforward_waldhausenExact f) n

end Quillen.PerfectComplexes
