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
    {X Y : Quillen.Scheme.LocallyNoetherianFiniteFlatSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ)
    (x : (Quillen.Scheme.KFiniteFlatPushforwardFunctor n).obj X) :
    (Quillen.Scheme.KToGFiniteFlatPushforward n).app Y
        ((Quillen.Scheme.KFiniteFlatPushforwardFunctor n).map f x) =
      ((Quillen.Scheme.forgetFiniteFlat ⋙ Quillen.Scheme.GFinitePushforwardFunctor n).map f)
        ((Quillen.Scheme.KToGFiniteFlatPushforward n).app X x) :=
  congrArg (fun h ↦ h x) ((Quillen.Scheme.KToGFiniteFlatPushforward n).naturality f)

end Consumer.FiniteFlatPushforward
