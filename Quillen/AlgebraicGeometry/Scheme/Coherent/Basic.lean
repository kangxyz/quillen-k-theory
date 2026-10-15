/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Property
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.Exact
public import Quillen.CategoryTheory.SmallModel.Abelian
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

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (FiniteTypeSheaves affineLocallyFiniteType affineLocallyFiniteType_isoClosed
  finiteTypeSheavesToModules finiteTypeSheaves_essentiallySmall)
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineLocallyFiniteType_cokernels affineLocallyFiniteType_containsZero
  affineLocallyFiniteType_finiteColimits affineLocallyFiniteType_finiteLimits
  affineLocallyFiniteType_kernels coherentExactStructure coherentInclusion
  coherent_shortExact_iff instAbelianCoherent noetherian_affineChart)
end Quillen.CoherentScheme

end



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
