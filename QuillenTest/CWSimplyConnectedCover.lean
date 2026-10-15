/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.SimplyConnectedCover

/-! # Actual classical CW cover regressions -/

@[expose] public section

open Topology
noncomputable section
open Set Quillen Quillen.ClassicalCW
universe u
namespace QuillenTest.CWSimplyConnectedCover
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- Local path connectedness refers to the original CW subtype topology. -/
theorem actual_local_path_connectedness : LocallyPathConnectedSpace C :=
  Quillen.ClassicalCW.locallyPathConnectedSpace C

/-- Actual ambient-null neighborhoods exist without any connectedness premise. -/
theorem open_ambient_null_neighborhood (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧ AmbientPathThin U :=
  exists_open_ambientPathThin C x

/-- The selected thin neighborhood is open in the original topology. -/
theorem selected_neighborhood_open (x : C) :
    IsOpen ((pathThinNeighborhoods C).neighborhood x) :=
  (pathThinNeighborhoods C).isOpen_neighborhood x

/-- The selected neighborhood contains precisely the originally requested point. -/
theorem selected_neighborhood_contains (x : C) :
    x ∈ (pathThinNeighborhoods C).neighborhood x :=
  (pathThinNeighborhoods C).mem_neighborhood x

/-- The selected neighborhood is genuinely pathconnected. -/
theorem selected_neighborhood_pathconnected (x : C) :
    IsPathConnected ((pathThinNeighborhoods C).neighborhood x) :=
  (pathThinNeighborhoods C).isPathConnected_neighborhood x

/-- Relative-endpoint paths in the neighborhood are homotopic in the original complex. -/
theorem actual_ambient_path_uniqueness (x : C) {a b : C} (p q : Path a b)
    (hp : ∀ t, p t ∈ (pathThinNeighborhoods C).neighborhood x)
    (hq : ∀ t, q t ∈ (pathThinNeighborhoods C).neighborhood x) : p.Homotopic q :=
  (pathThinNeighborhoods C).ambientPathThin x p q hp hq

/-- Connectedness of the original subtype suffices for the same-universe actual cover. -/
theorem actual_cover_existence [ConnectedSpace C] :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : C(E, C)),
      IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace E :=
  exists_simplyConnected_cover C

end QuillenTest.CWSimplyConnectedCover
