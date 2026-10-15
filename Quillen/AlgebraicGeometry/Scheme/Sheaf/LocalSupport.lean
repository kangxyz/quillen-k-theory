/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support

/-!
# Closed support from finite affine local models

Closedness of the actual stalk support can be checked on any scheme open
cover. In particular, an affine open cover on which a sheaf is quasi-coherent
with finitely generated section modules yields closed support on the whole
scheme. The local hypotheses are actual sheaf and module conditions; no
closed-support conclusion is supplied as finiteness data.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Closedness of stalk support is local for an actual open cover of schemes. -/
theorem isClosed_support_iff_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{v})
    (M : X.Modules) :
    IsClosed (support M) ↔
      ∀ i, IsClosed (support ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj M)) := by
  constructor
  · intro h i
    rw [support_restrict]
    exact h.preimage (𝒰.f i).continuous
  · intro h
    rw [← isOpen_compl_iff]
    apply (isOpen_iff_of_cover
      (fun i => (𝒰.f i).isOpenEmbedding.isOpen_range) 𝒰.iUnion_range).2
    intro i
    rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    rw [Set.preimage_compl, ← support_restrict]
    exact (h i).isOpen_compl

/-- Finite modules on an affine open cover give closed support of the sheaf.
This does not impose noetherianity: the local finite-module criterion itself
suffices. -/
theorem isClosed_support_of_finite_affineCover {X : Scheme.{u}}
    (𝒰 : X.AffineOpenCover.{v}) (M : X.Modules)
    [∀ i, ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj M).IsQuasicoherent]
    [∀ i, Module.Finite (𝒰.X i)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj M))] :
    IsClosed (support M) := by
  apply (isClosed_support_iff_openCover 𝒰.openCover M).2
  intro i
  exact isClosed_support_of_finite_globalSections
    ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj M)

end AlgebraicGeometry.Scheme.Modules
