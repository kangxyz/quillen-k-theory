/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.PathComponent

/-!
# Path-component fundamental-group consumers

Component inclusion detects homotopy of the original loops, and every ambient
loop is represented by its codomain restriction. The comparison also transfers
commutativity to the existing first homotopy group on the component.
-/

@[expose] public section

noncomputable section

universe u

namespace QuillenTest.PathComponentFundamentalGroup

open Quillen

variable {X : Type u} [TopologicalSpace X] (x : X)

/-- An ambient homotopy between included component loops already lies in the component. -/
theorem original_loop_homotopy_detection
    (p q : Path (⟨x, mem_pathComponent_self x⟩ : pathComponent x)
      ⟨x, mem_pathComponent_self x⟩)
    (h : (p.map continuous_subtype_val).Homotopic (q.map continuous_subtype_val)) :
    p.Homotopic q := by
  obtain ⟨H⟩ := h
  exact ⟨pathComponentHomotopy H⟩

/-- The equivalence sends the actual restricted loop to the original ambient loop. -/
theorem original_loop_restriction (p : Path x x) :
    pathComponentFundamentalGroupEquiv x
      (Path.Homotopic.Quotient.mk
        (pathComponentPath (a := ⟨x, mem_pathComponent_self x⟩)
          (b := ⟨x, mem_pathComponent_self x⟩) p)) =
      Path.Homotopic.Quotient.mk p := by
  change Path.Homotopic.Quotient.mk
    ((pathComponentPath (a := ⟨x, mem_pathComponent_self x⟩)
      (b := ⟨x, mem_pathComponent_self x⟩) p).map continuous_subtype_val) = _
  rw [pathComponentPath_map]

/-- The original inclusion-induced map detects nullhomotopic component loops. -/
theorem original_inclusion_detects_one
    (a : FundamentalGroup (pathComponent x) ⟨x, mem_pathComponent_self x⟩)
    (h : FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X))
      ⟨x, mem_pathComponent_self x⟩ a = 1) : a = 1 := by
  apply (pathComponentFundamentalGroupEquiv x).injective
  simpa only [map_one, pathComponentFundamentalGroupEquiv_apply] using h

/-- Ambient first-homotopy-group commutativity survives restriction without new operations. -/
theorem original_pi_one_commutativity
    (h : ∀ a b : HomotopyGroup.Pi 1 X x, a * b = b * a)
    (a b : HomotopyGroup.Pi 1 (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    a * b = b * a :=
  pathComponentPiOne_mul_comm x h a b

end QuillenTest.PathComponentFundamentalGroup
