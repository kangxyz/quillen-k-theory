/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affine-locally quasicoherent sheaves of finite type

The predicate is imposed on every actual affine open chart: its restriction
is quasicoherent with finite global sections. All affine charts are tested;
no noetherianity condition is used to filter the charts. When the ambient
scheme is locally noetherian, chart rings are proved noetherian, and closure
under ambient finite limits and colimits follows from the affine theorem.

Under local noetherianity, the resulting full category is abelian and its
exact sequences are actual sheaf exact sequences. The initial G-theory definition uses a small model
  in
the upper universe `u+1`; lowest-universe essential smallness and comparison
with the earlier affine small model are separate results.
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
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- G-theory of a locally noetherian scheme, initially formed in the upper
sheaf-object universe. No lowest-universe shrinking assertion is implicit. -/
abbrev G (n : ℕ) : Type (u+1) := CategoryTheory.ExactCategory.ExactStructure.SmallK.{u+1}
  (coherentExactStructure X) n

end AlgebraicGeometry.Scheme.Modules.Coherent
