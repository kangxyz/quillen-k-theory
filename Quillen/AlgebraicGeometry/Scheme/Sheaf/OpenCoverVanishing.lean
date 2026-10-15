/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Support

/-! # Vanishing detected on arbitrary actual open covers -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules



noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
/-- Actual module sheaves vanish if their restrictions to any open cover vanish. -/
theorem isZero_of_openCover {X : Scheme.{u}} (M : X.Modules) {ι : Type w}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hM : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (U i).ι).obj M)) : IsZero M := by
  apply (isZero_iff_stalks M).mpr
  intro x
  obtain ⟨i,hi⟩ := hU x
  exact ((stalkFunctor (U i).toScheme ⟨x,hi⟩).map_isZero (hM i)).of_iso
    ((Scheme.Modules.restrictStalkNatIso (U i).ι ⟨x,hi⟩).app M).symm
end AlgebraicGeometry.Scheme.Modules
