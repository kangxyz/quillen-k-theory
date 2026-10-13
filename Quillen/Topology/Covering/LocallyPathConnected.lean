/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Actual local charts give local path connectedness upstairs

Source-only draft. Open local-homeomorphism charts inherit local path
connectedness from the original base. Their actual open subtype neighborhoods
then give neighborhoods in the original total topology.
-/

@[expose] public section
noncomputable section
open Set Topology
universe u v
namespace Quillen.Covering

variable {T : Type u} {X : Type v} [TopologicalSpace T] [TopologicalSpace X]
  [LocallyPathConnectedSpace X]

/-- Local homeomorphism charts transfer local path connectedness to the actual source space. -/
theorem locallyPathConnectedSpace_of_isLocalHomeomorph {p : T → X}
    (hp : IsLocalHomeomorph p) : LocallyPathConnectedSpace T := by
  apply locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
  intro x O hO hx
  obtain ⟨e, hxe, _he⟩ := hp x
  let := e.isOpenEmbedding_restrict.locallyPathConnectedSpace
  let x' : e.source := ⟨x, hxe⟩
  let V : Set e.source := Subtype.val ⁻¹' O
  have hV : IsOpen V := hO.preimage continuous_subtype_val
  have hxV : x' ∈ V := hx
  refine mem_nhds_iff.mpr ⟨Subtype.val '' pathComponentIn V x', ?_,
    e.open_source.isOpenMap_subtype_val _ (hV.pathComponentIn x'), ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨hz.somePath.map continuous_subtype_val, fun t => hz.somePath_mem t⟩
  · exact ⟨x', mem_pathComponentIn_self hxV, rfl⟩

/-- A genuine covering over an LPC base has an LPC total space, without a surjectivity premise. -/
theorem locallyPathConnectedSpace_total {p : T → X} (hp : IsCoveringMap p) :
    LocallyPathConnectedSpace T :=
  locallyPathConnectedSpace_of_isLocalHomeomorph hp.isLocalHomeomorph

end Quillen.Covering
