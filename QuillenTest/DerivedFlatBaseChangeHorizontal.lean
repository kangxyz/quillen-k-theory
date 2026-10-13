/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeLocalization

/-! # Original-map consumers of horizontal derived flat base change -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.SchemeSheaf
attribute [local instance] Abelian.hasFiniteBiproducts
namespace QuillenTest.DerivedFlatBaseChangeHorizontal

open Quillen
/-- The actual standard ambient module-sheaf derived categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j) [Flat k] [Flat j]
/-- The inverse composition retains the inverse original geometric comparison. -/
theorem original_inverse_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pullback (k ≫ j)).rightDerivedFunctorPlusUnit.app K ≫
      (derivedFlatPullbackPlusCompIso k j).inv.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp k j)).inv.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback j)
        (Scheme.Modules.pullback k)).app K :=
  derivedFlatPullbackPlusCompIso_inv_unit k j K
/-- The pasted mate itself has the literal four-arrow component. -/
theorem original_pasted_mate (K : DerivedCategory.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    (derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app K =
      (derivedFlatPullbackPlusCompIso k j).inv.app ((derivedPushforwardPlus f).obj K) ≫
      (derivedFlatPullbackPlus k).map ((derivedFlatBaseChangeMap a b f j h).app K) ≫
      (derivedFlatBaseChangeMap c d b k hs).app ((derivedFlatPullbackPlus a).obj K) ≫
      (derivedPushforwardPlus d).map ((derivedFlatPullbackPlusCompIso c a).hom.app K) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  rw [← derivedFlatBaseChangeMap_paste_horiz c d k a b f j hs h]
  exact derivedFlatBaseChangeHorizontalComposite_app c d k a b f j hs h K
/-- The original ordinary mate remains the arrow in the composite-unit square. -/
theorem original_ordinary_mate (K : CochainComplex.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback (k ≫ j))).app K ≫
      (derivedFlatBaseChangeHorizontalComposite c d k a b f j hs h).app
        (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus
          (cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h))).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback (c ≫ a))
        (Scheme.Modules.pushforward d)).app K :=
  derivedFlatBaseChangeHorizontalComposite_unit c d k a b f j hs h K
/-- Naturality acts on the original pasted-square functors and on the composite mate. -/
theorem original_arrow_naturality {K L : DerivedCategory.Plus U.Modules} (q : K ⟶ L) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    (derivedFlatPullbackPlus (k ≫ j)).map ((derivedPushforwardPlus f).map q) ≫
        (derivedFlatBaseChangeHorizontalComposite c d k a b f j hs h).app L =
      (derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app K ≫
        (derivedPushforwardPlus d).map ((derivedFlatPullbackPlus (c ≫ a)).map q) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  rw [derivedFlatBaseChangeMap_paste_horiz c d k a b f j hs h]
  exact (derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).naturality q
/-- Local invertibility gives a genuine inverse to the original restricted derived arrow. -/
theorem original_localized_inverse [IsOpenImmersion k] (K : DerivedCategory.Plus U.Modules)
    (hK : IsIso ((derivedFlatBaseChangeMap (c ≫ a) d f (k ≫ j)
      (hs.paste_horiz h)).app K)) :
    letI := flat_cartesian_baseChange a b f j h
    letI := flat_cartesian_baseChange c d b k hs
    ∃ q, (derivedFlatPullbackPlus k).map
        ((derivedFlatBaseChangeMap a b f j h).app K) ≫ q = 𝟙 _ ∧
      q ≫ (derivedFlatPullbackPlus k).map
        ((derivedFlatBaseChangeMap a b f j h).app K) = 𝟙 _ := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b k hs
  have := (isIso_derivedFlatBaseChangeMap_pullback_iff c d k a b f j hs h K).mpr hK
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩
end QuillenTest.DerivedFlatBaseChangeHorizontal
