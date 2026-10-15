/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Comparison.KToGFinitePushforward

/-! Independent use of the covariant finite flat K-to-G natural comparison. -/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace Consumer.FiniteFlatPushforward

/-- The public natural comparison commutes on every original K-class. -/
theorem comparison_on_elements
    {X Y : AlgebraicGeometry.Scheme.LocallyNoetherianFiniteFlatSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (x : (AlgebraicGeometry.Scheme.KFiniteFlatPushforwardFunctor n).obj X) :
    (AlgebraicGeometry.Scheme.KToGFiniteFlatPushforward n).app Y
        ((AlgebraicGeometry.Scheme.KFiniteFlatPushforwardFunctor n).map f x) =
      ((AlgebraicGeometry.Scheme.forgetFiniteFlat ⋙
        AlgebraicGeometry.Scheme.GFinitePushforwardFunctor n).map f)
        ((AlgebraicGeometry.Scheme.KToGFiniteFlatPushforward n).app X x) :=
  congrArg (fun h ↦ h x) ((AlgebraicGeometry.Scheme.KToGFiniteFlatPushforward n).naturality f)

end Consumer.FiniteFlatPushforward
