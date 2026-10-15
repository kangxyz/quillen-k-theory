/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeSupport
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.GTheory
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support

/-!
# Actual supported coherent sheaves on a noetherian affine scheme

The support category is the kernel of actual open restriction, applied to
actual coherent sheaves. Its Serre property is proved from exactness of the
inclusion and restriction functors. Its objects have ordinary closed stalk
support, and vanishing on the open is equivalent to support in its complement.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

variable {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- G-theory with support, formed from the actual supported coherent category. -/
abbrev SupportedAffineG (n : ℕ) : Type u :=
  CategoryTheory.ExactCategory.ExactStructure.SmallK.{u} (supportedAffineCoherentExactStructure R j)
    n

end AlgebraicGeometry.Scheme.Modules.Coherent
