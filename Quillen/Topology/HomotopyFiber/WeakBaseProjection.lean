/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.WeakPullback
public import Quillen.Topology.HomotopyFiber.ProjectionFibration
public import Quillen.Topology.HomotopyPullback.Symmetry
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceCancellation

/-! # The original fiber projection over a weakly contractible base -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Quillen.HomotopyFiber
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- The actual point inclusion is weak whenever the base's map to a point is weak. -/
theorem pointInclusion_isWeakHomotopyEquivalence (b : B)
    (hB : IsWeakHomotopyEquivalence (ContinuousMap.const B (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence (ContinuousMap.const (ULift.{u} Unit) b) := by
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv
    (Homeomorph.homeomorphOfUnique (ULift.{u} Unit) PUnit.{u + 1}).toHomotopyEquiv
  have hc : IsWeakHomotopyEquivalence
      ((ContinuousMap.const B (PUnit.unit : PUnit.{u + 1})).comp
        (ContinuousMap.const (ULift.{u} Unit) b)) := h
  exact hc.of_comp_right hB

/-- Weak contractibility suffices for the actual homotopy-fiber projection,
without choosing a contraction or using a Whitehead theorem. -/
theorem projection_isWeakHomotopyEquivalence_of_weakBase (p : C(E, B)) (b : B)
    (hB : IsWeakHomotopyEquivalence (ContinuousMap.const B (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence (projection p b) := by
  let q : C(ULift.{u} Unit, B) := ContinuousMap.const _ b
  have hq : IsWeakHomotopyEquivalence q := pointInclusion_isWeakHomotopyEquivalence b hB
  have hs := (HomotopyPullback.baseProjection_isWeakHomotopyEquivalence q p hq).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (HomotopyPullback.symmetryHomeomorph p q).toHomotopyEquiv)
  exact hs.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (constantParameterHomeomorph p b).toHomotopyEquiv)

end Quillen.HomotopyFiber
