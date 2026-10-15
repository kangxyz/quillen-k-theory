/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Restriction

/-!
# Public scheme K-theory interface

`Quillen.Scheme.K X n` is genuine K-theory of finite locally free sheaves.
For `X : AlgebraicGeometry.Scheme.{u}` it lives in `Type (u + 1)`, using the
proved upper-universe small presentation. Open restriction uses the actual
geometric exact functor. No cross-universe comparison is asserted here.
-/
@[expose] public section
open Quillen


noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

/-- Genuine scheme K-theory in the explicitly chosen small universe `u + 1`. -/
abbrev K (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  AlgebraicGeometry.Scheme.Modules.SchemeK X n

/-- Actual open restriction on scheme K-groups. -/
def restrictK {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : K X n →* K U n :=
  AlgebraicGeometry.Scheme.Modules.schemeKRestrict j n

/-- The public map is exactly the canonical K-map of vector-bundle restriction. -/
@[simp] theorem restrictK_eq_smallKMap {U X : AlgebraicGeometry.Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    restrictK j n = (AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict j).smallKMap n :=
      rfl

end AlgebraicGeometry.Scheme
