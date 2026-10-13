/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.OpenGluing.RightChart
public import Quillen.Topology.FiberwiseBridge.TargetCollar

/-! # Actual right normalized collar and weak endpoint comparisons

The right mapping cylinder supplies the genuine right target collar. Its full
ambient-base equation is proved after flipping the original displayed bridge
pushout. The final maps are the unchanged right chart endpoint and its literal
base changes; actual right bridge-end weakness remains explicit.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.NormalizedFibrationSpan.Data
open TheoremB FiberwiseMappingPath
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)

/-- The bridge height measured from the right mapping cylinder, using the flipped bridge pushout. -/
def rightBridgeTargetHeight : C(d.Bridge,unitInterval) :=
  Quillen.FiberwiseBridge.TargetCollar.height d.cylinder1 d.bridge_isPushout.flip

@[simp] theorem rightBridgeTargetHeight_target (a : d.Q1) :
    d.rightBridgeTargetHeight (d.normalized.i1 a) = 1 :=
  Quillen.FiberwiseBridge.TargetCollar.height_target d.cylinder1 d.bridge_isPushout.flip a

/-- The strong deformation retraction of the right bridge target collar onto its endpoint, for
`cut < 1` and the right-cylinder height. -/
def normalizedRightBridgeEndCollarSDR (cut : unitInterval) (hc : cut < 1) :
    Quillen.CylinderStrongDeformationRetract
      (d.normalized.swapped.bridgeEndCollarEnd d.rightBridgeTargetHeight
        d.rightBridgeTargetHeight_target cut hc) :=
  Quillen.FiberwiseBridge.TargetCollar.strongDeformationRetract d.cylinder1
    d.bridge_isPushout.flip cut hc

/-- Reversing the displayed bridge pushout retains exactly its original base map. -/
theorem bridgeProjection_flipped :
    Quillen.FiberwiseBridge.projection d.cylinder1 d.cylinder0 d.bridge_isPushout.flip
      d.q1 d.q0 d.square.symm = d.bridgeProjection := by
  apply d.bridge_isPushout.hom_ext
  · exact (Quillen.FiberwiseBridge.projection_right d.cylinder1 d.cylinder0 d.bridge_isPushout.flip
      d.q1 d.q0 d.square.symm).trans
      (Quillen.FiberwiseBridge.projection_left d.cylinder0 d.cylinder1 d.bridge_isPushout
        d.q0 d.q1 d.square).symm
  · exact (Quillen.FiberwiseBridge.projection_left d.cylinder1 d.cylinder0 d.bridge_isPushout.flip
      d.q1 d.q0 d.square.symm).trans
      (Quillen.FiberwiseBridge.projection_right d.cylinder0 d.cylinder1 d.bridge_isPushout
        d.q0 d.q1 d.square).symm

theorem normalizedRightBridgeEndCollarSDR_over (cut : unitInterval) (hc : cut < 1) :
    (d.normalizedRightBridgeEndCollarSDR cut hc).H ≫
        d.normalized.swapped.bridgeEndCollarBase d.rightBridgeTargetHeight cut =
      fst (d.normalized.swapped.BridgeEndCollar d.rightBridgeTargetHeight cut) TopCat.I ≫
        d.normalized.swapped.bridgeEndCollarBase d.rightBridgeTargetHeight cut := by
  have hR := Quillen.FiberwiseBridge.TargetCollar.deformation_over d.cylinder1
    d.bridge_isPushout.flip
    cut d.cylinder0 d.q1 d.q0 d.square.symm hc
  rw [d.bridgeProjection_flipped] at hR
  apply ConcreteCategory.hom_ext
  intro z
  exact congrArg (fun x : (U ∩ V : Set T) ↦ x.val) (ConcreteCategory.congr_hom hR z)

theorem rightEnd_isWeakHomotopyEquivalence (hU : IsOpen U) (hV : IsOpen V)
    (hweak : IsWeakHomotopyEquivalence d.normalized.i1.hom) :
    IsWeakHomotopyEquivalence d.normalized.rightEnd.hom :=
  d.normalized.rightEnd_isWeakHomotopyEquivalence d.rightBridgeTargetHeight
    d.rightBridgeTargetHeight_target 0 zero_lt_one hU hV
    (d.normalizedRightBridgeEndCollarSDR 0 zero_lt_one) hweak

theorem rightEnd_baseChange_isWeakHomotopyEquivalence
    {D : Type u} [TopologicalSpace D] (g : C(D, T)) (hU : IsOpen U) (hV : IsOpen V)
    (hweak : IsWeakHomotopyEquivalence
      (baseChangedMap d.normalized.bridgeBase.hom d.normalized.i1.hom g)) :
    IsWeakHomotopyEquivalence
      (baseChangedMap d.normalized.rightBase.hom d.normalized.rightEnd.hom g) :=
  d.normalized.rightEnd_baseChange_isWeakHomotopyEquivalence d.rightBridgeTargetHeight
    d.rightBridgeTargetHeight_target 0 zero_lt_one hU hV
    (d.normalizedRightBridgeEndCollarSDR 0 zero_lt_one)
    (d.normalizedRightBridgeEndCollarSDR_over 0 zero_lt_one) g hweak

end Quillen.NormalizedFibrationSpan.Data
