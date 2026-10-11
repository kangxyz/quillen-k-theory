/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.SmallModel

/-! Consumers keep independent original object/hom universes and the literal
original algebraic presentation and homotopical K₀ at both endpoints. -/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.Waldhausen
universe u v
namespace Quillen.Tests.WaldhausenUniverseComparison
open AlgebraicGrothendieck
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)

/-- The genuine up/down presentation maps retain every original algebraic class. -/
theorem original_presentation_round_trip (a : Group W) :
    AlgebraicGrothendieck.map W.smallModel AsSmall.down W.smallModel_down_exact
      (AlgebraicGrothendieck.map W AsSmall.up W.smallModel_up_exact a) = a :=
  DFunLike.congr_fun (smallModel_down_comp_up W) a

/-- The actual original object loop survives the genuine based universe-lifting equivalence. -/
theorem original_object_loop_lifts (A : C) :
    W.smallModelKEquiv 0 (W.kZeroObjectClass A) =
      W.smallModel.kZeroObjectClass (AsSmall.up.obj A) := W.smallModelKEquiv_objectClass A

/-- Every actual original fine K₀ class is retained by the full independent-universe comparison. -/
theorem original_fine_round_trip (x : W.K 0) :
    grothendieckKZeroEquivOfSmallModel W ((grothendieckKZeroEquivOfSmallModel W).symm x) = x :=
  (grothendieckKZeroEquivOfSmallModel W).apply_symm_apply x

/-- The inverse retains original exact-functor maps on every actual original class. -/
theorem original_exact_functor_inverse (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F) (x : W.K 0) :
    (grothendieckKZeroEquivOfSmallModel V).symm (KMap hF 0 x) =
      (AlgebraicGrothendieck.map W F hF).toMultiplicative
        ((grothendieckKZeroEquivOfSmallModel W).symm x) :=
  grothendieckKZeroEquivOfSmallModel_symm_natural W V F hF x

/-- On the prior matching-universe scope, the new public comparison is literally the prior one. -/
theorem original_small_comparison_unchanged {C₀ : Type u} [SmallCategory C₀]
    (W₀ : Structure C₀) : grothendieckKZeroEquivOfSmallModel W₀ = grothendieckKZeroEquiv W₀ :=
  grothendieckKZeroEquivOfSmallModel_eq W₀

end Quillen.Tests.WaldhausenUniverseComparison
