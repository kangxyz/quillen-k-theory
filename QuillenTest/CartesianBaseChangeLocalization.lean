/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChangeLocalization

/-! # Literal horizontal mate and target-open localization consumers -/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.CartesianBaseChangeLocalization

open AlgebraicGeometry.Scheme.Modules Scheme.Modules
variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j)
/-- The actual geometric unit retains both original composition comparisons. -/
theorem original_composite_unit (M : U.Modules) :
    (pullbackPushforwardAdjunction a).unit.app M ≫
      (pushforward a).map ((pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback a).obj M)) ≫
      (pushforward a).map ((pushforward c).map ((pullbackComp c a).hom.app M)) ≫
      (pushforwardComp c a).hom.app ((Scheme.Modules.pullback (c ≫ a)).obj M) =
      (pullbackPushforwardAdjunction (c ≫ a)).unit.app M :=
  pullbackAdjunctionUnit_comp c a M
/-- The horizontal equation retains the literal two pullback composition maps. -/
theorem original_horizontal_mate (M : U.Modules) :
    (pullbackComp k j).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app M =
      (Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app M) ≫
        (cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj M) ≫
        (pushforward d).map ((pullbackComp c a).hom.app M) :=
  cartesianBaseChangeMap_paste_horiz c d k a b f j hs h M
/-- The localized isomorphism criterion concerns the same original mate. -/
theorem original_localized_iff [IsOpenImmersion k] (M : U.Modules) :
    IsIso ((Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app M)) ↔
      IsIso ((cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app M) :=
  isIso_cartesianBaseChangeMap_pullback_iff c d k a b f j hs h M
/-- Actual localized mates on a genuine cover invert the original global arrow. -/
theorem original_cover_reflection {ι : Type v} (Y Z : ι → Scheme.{u})
    (k : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (k i)]
    (c : ∀ i, Z i ⟶ W) (d : ∀ i, Z i ⟶ Y i)
    (hs : ∀ i, IsPullback (c i) (d i) b (k i))
    (hcover : ∀ x : V, ∃ (i : ι) (y : Y i), k i y = x)
    (M : U.Modules)
    (hM : ∀ i, IsIso ((cartesianBaseChangeMap (c i ≫ a) (d i) f (k i ≫ j)
      ((hs i).paste_horiz h)).app M)) : IsIso ((cartesianBaseChangeMap a b f j h).app M) :=
  isIso_cartesianBaseChangeMap_of_openCover a b f j h Y Z k c d hs hcover M hM
end QuillenTest.CartesianBaseChangeLocalization
