/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedOpenCoverConservativity
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeLocalization
/-! # Open-cover detection for the original derived flat base-change map

A genuine target-open cover detects invertibility of the original derived mate through the
mates of its actual horizontally pasted squares. The local invertibility assumptions are
explicit; no general flat base-change invertibility is inferred. -/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The original standard derived categories of module sheaves. -/
local instance baseChangeOpenCoverStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
/-- Local original pasted mates detect invertibility of the original derived flat mate. -/
theorem isIso_derivedFlatBaseChangeMap_of_openCover
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j] {ι : Type v} (Y Z : ι → Scheme.{u})
    (k : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (k i)]
    (c : ∀ i, Z i ⟶ W) (d : ∀ i, Z i ⟶ Y i)
    (hs : ∀ i, IsPullback (c i) (d i) b (k i))
    (hcover : ∀ x : V, ∃ (i : ι) (y : Y i), k i y = x)
    (K : DerivedCategory.Plus U.Modules)
    (hK : ∀ i, IsIso ((derivedFlatBaseChangeMap (c i ≫ a) (d i) f (k i ≫ j)
      ((hs i).paste_horiz h)).app K)) :
    letI := flat_cartesian_baseChange a b f j h
    IsIso ((derivedFlatBaseChangeMap a b f j h).app K) := by
  let := flat_cartesian_baseChange a b f j h
  apply isIso_of_derivedOpenPullback_openCover Y k hcover
  intro i
  exact (isIso_derivedFlatBaseChangeMap_pullback_iff (c i) (d i) (k i) a b f j
    (hs i) h K).mpr (hK i)
end AlgebraicGeometry.Scheme.Modules
