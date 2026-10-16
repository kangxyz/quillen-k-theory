/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.Affine

/-!
# Finite projective dimension and affine resolutions

Objectwise finite Ext-defined projective dimension of finite modules gives actual finite locally
free coherent resolutions on a noetherian affine scheme.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- Objectwise Ext-defined finite projective dimension produces the actual
affine finite-vector-bundle-resolution hypothesis. This is a homological
intermediate statement, not a substituted regularity assumption. -/
theorem coherentResolutionHypothesis_of_finite_projectiveDimension
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (h : ∀ M : ModuleCat.FiniteModule.{u, u} R,
      projectiveDimension M.obj ≠ ⊤) :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure (Spec R)).ResolutionHypothesis
      (coherentVectorBundle (Spec R)) := by
  intro M
  let N := (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence
    R).functor.obj M
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff N.obj).mp (h N)
  have := hn
  obtain ⟨T, _⟩ := coherentResolution_length_le_of_projectiveDimensionLE R n M
  exact ⟨T⟩

end AlgebraicGeometry.Scheme.Modules
