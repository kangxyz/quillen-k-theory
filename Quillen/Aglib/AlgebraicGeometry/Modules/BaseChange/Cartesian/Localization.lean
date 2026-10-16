/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian.Horizontal
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Cartesian.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Target-open localization of the original geometric base-change mate -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules

variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j) [IsOpenImmersion k]

/-- Invertibility of the original base-change mate after an actual open pullback is equivalent
to invertibility of the mate of the horizontally pasted square. -/
theorem isIso_cartesianBaseChangeMap_pullback_iff (M : U.Modules) :
    IsIso ((Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app M)) ↔
      IsIso ((cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app M) := by
  let : IsOpenImmersion c := MorphismProperty.of_isPullback hs.flip inferInstance
  have := isIso_cartesianBaseChangeMap_of_open c d b k hs
  rw [← isIso_comp_left_iff ((pullbackComp k j).hom.app ((pushforward f).obj M))]
  rw [cartesianBaseChangeMap_paste_horiz c d k a b f j hs h M]
  rw [← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
universe v

/-- Actual target-open localizations detect invertibility of the original geometric mate. -/
theorem isIso_cartesianBaseChangeMap_of_openCover
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) {ι : Type v} (Y Z : ι → Scheme.{u})
    (k : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (k i)]
    (c : ∀ i, Z i ⟶ W) (d : ∀ i, Z i ⟶ Y i)
    (hs : ∀ i, IsPullback (c i) (d i) b (k i))
    (hcover : ∀ x : V, ∃ (i : ι) (y : Y i), k i y = x)
    (M : U.Modules)
    (hM : ∀ i, IsIso ((cartesianBaseChangeMap (c i ≫ a) (d i) f (k i ≫ j)
      ((hs i).paste_horiz h)).app M)) : IsIso ((cartesianBaseChangeMap a b f j h).app M) := by
  apply isIso_of_restrict_openCover Y k hcover
  intro i
  have := (isIso_cartesianBaseChangeMap_pullback_iff (c i) (d i) (k i) a b f j
    (hs i) h M).mpr (hM i)
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (k i)) _).mpr
    inferInstance

end AlgebraicGeometry.Scheme.Modules
