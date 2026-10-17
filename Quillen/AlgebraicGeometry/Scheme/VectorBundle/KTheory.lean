/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.SmallModel

public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Quillen.CategoryTheory.SmallModel.Exact

/-!
# Quillen K-theory of an actual scheme

For an arbitrary scheme `X : Scheme.{u}`, define `SchemeK X n` using the exact
category of finite locally free `𝒪_X`-module sheaves, with all ambient short
exact sequences as conflations. We use the genuine categorical small model
in the explicitly enlarged universe `u + 1`. This requires neither a
noetherian hypothesis nor an unproved essential-smallness theorem in the
smaller universe `u`.

This file does not identify realizations across universe changes. Independence
of exact presentations within the chosen universe is provided by
`CategoryTheory.ExactCategory.ExactStructure.presentationKEquiv`.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.ExactCategory

open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- Genuine scheme K-theory, formed from finite locally free sheaves and their
ambient short exact sequences in the explicitly enlarged small universe. -/
abbrev SchemeK (X : Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  CategoryTheory.ExactCategory.ExactStructure.SmallK.{u + 1} (vectorBundleExactStructure X) n

/-- The ambient sheaf inclusion induces its canonical map on K-groups.
The target is K-theory of all module sheaves, not coherent G-theory. -/
def schemeKToModuleSheafK (X : Scheme.{u}) (n : ℕ) :
    SchemeK X n →* CategoryTheory.ExactCategory.ExactStructure.SmallK.{u + 1} (sheafExactStructure
      X) n :=
  (vectorBundleExactInclusion X).smallKMap n

end AlgebraicGeometry.Scheme.Modules
