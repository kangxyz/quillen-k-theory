/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support

/-!
# Closed stalk support of actual global coherent sheaves

Finite global sections on each actual affine chart give closed support on
that chart. Since affine open charts cover the scheme, the ordinary global
stalk support is closed. This is proved directly from the affine-local
condition, without a global finiteness or separatedness hypothesis.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- The ordinary stalk support of a sheaf satisfying the actual affine-local
finite quasicoherent condition is closed. -/
theorem isClosed_support_of_coherent {X : Scheme.{u}} {M : X.Modules} (hM : affineLocallyFiniteType
  X M) :
    IsClosed (AlgebraicGeometry.Scheme.Modules.support M) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let i := X.affineOpenCover.idx x
  let j := X.affineOpenCover.f i
  obtain ⟨y, hy⟩ := X.affineOpenCover.covers x
  have hC := hM (X.affineOpenCover.X i) j
  have : ((Scheme.Modules.restrictFunctor j).obj M).IsQuasicoherent := hC.1
  have : Module.Finite (X.affineOpenCover.X i)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor j).obj M)) := hC.2
  have hc : IsClosed (j ⁻¹' AlgebraicGeometry.Scheme.Modules.support M) := by
    rw [← AlgebraicGeometry.Scheme.Modules.support_restrict j M]
    exact AlgebraicGeometry.Scheme.Modules.isClosed_support_of_finite_globalSections _
  have ho : IsOpen (j '' (j ⁻¹' AlgebraicGeometry.Scheme.Modules.support M)ᶜ) :=
    j.isOpenEmbedding.isOpenMap _ hc.isOpen_compl
  apply Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · refine ⟨y, ?_, hy⟩
    change j y ∉ AlgebraicGeometry.Scheme.Modules.support M
    rw [show j y = x from hy]
    exact hx
  · rintro z ⟨w, hw, rfl⟩
    exact hw

/-- The actual affine-local finite-type sheaf objects have closed support on every scheme;
no noetherian hypothesis is needed for this support statement. -/
theorem coherent_support_isClosed {X : Scheme.{u}} (M : FiniteTypeSheaves X)
  :
    IsClosed (AlgebraicGeometry.Scheme.Modules.support M.obj) := isClosed_support_of_coherent
      M.property

end AlgebraicGeometry.Scheme.Modules.Coherent
