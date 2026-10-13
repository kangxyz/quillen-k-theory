/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.Connectivity
public import Quillen.Topology.HomotopyEquiv.ComponentSigma
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Open path components of realizations and dominated spaces

Each topological simplex is path connected, so its inverse image of any
realization path component is empty or the entire simplex. The actual final
colimit topology therefore makes every realization path component open.
Actual domination maps and their homotopy transfer this property to the
dominated space. No domination maps for a new space are postulated here.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

/-- A map from a path-connected space meets an ambient component either everywhere or nowhere. -/
theorem isOpen_preimage_pathComponent_of_pathConnected
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (f : C(X, Y)) (y : Y) :
    IsOpen (f ⁻¹' pathComponent y) := by
  by_cases h : (f ⁻¹' pathComponent y).Nonempty
  · obtain ⟨x, hx⟩ := h
    have he : f ⁻¹' pathComponent y = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      exact hx.trans ((PathConnectedSpace.joined x z).map f.continuous)
    rw [he]
    exact isOpen_univ
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact isOpen_empty

/-- The actual realization topology has open path components. -/
theorem realization_isOpen_pathComponent (T : SSet.{u}) (x : |T|) :
    IsOpen (pathComponent x) := by
  let F := CostructuredArrow.proj SSet.stdSimplex T ⋙ SimplexCategory.toTop
  let e := TopCat.homeoOfIso
    (SSet.stdSimplex.leftKanExtensionObjIsoColimit SimplexCategory.toTop T)
  have ho : IsOpen (pathComponent (e x)) := by
    apply (TopCat.colimit_isOpen_iff F _).mpr
    intro j
    let : PathConnectedSpace (F.obj j) := by
      change PathConnectedSpace (SimplexCategory.toTop.obj j.left)
      infer_instance
    exact isOpen_preimage_pathComponent_of_pathConnected (colimit.ι F j).hom (e x)
  have hp := ho.preimage e.continuous
  simpa only [e.preimage_pathComponent, e.symm_apply_apply] using hp

/-- Genuine realization domination is enough for open components of the original space. -/
theorem realizationDominated_isOpen_pathComponent
    {X : Type u} [TopologicalSpace X] (T : SSet.{u})
    (a : C(X, |T|)) (b : C(|T|, X))
    (H : (b.comp a).Homotopy (ContinuousMap.id X)) (x : X) :
    IsOpen (pathComponent x) :=
  isOpen_pathComponent_of_domination a b H (realization_isOpen_pathComponent T) x

end Quillen
