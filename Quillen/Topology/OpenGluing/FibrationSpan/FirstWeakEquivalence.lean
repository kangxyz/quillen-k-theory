/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.OpenGluing.FirstWeakEquivalence
public import Quillen.Topology.FiberwiseBridge.TargetCollar

/-! # The original normalized fibration-span first end is weak

The actual mapping cylinders construct every local collar input. Only the
ordinary weak property of the unchanged bridge end remains as a hypothesis.
No global deformation of the bridge or projection lifting is inferred.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.NormalizedFibrationSpan.Data
variable {T : TopCat.{u}} {U V : Set T} (d : NormalizedFibrationSpan.Data T U V)

/-- The generic local SDR input is supplied by the original left mapping
cylinder's target collar, with exactly the original normalized attaching map. -/
def normalizedBridgeEndCollarSDR (cut : unitInterval) (hc : cut < 1) :
    TheoremA.CylinderStrongDeformationRetract
      (d.normalized.bridgeEndCollarEnd d.bridgeTargetHeight
        d.bridgeTargetHeight_target cut hc) :=
  d.bridgeTargetCollarSDR cut hc

/-- Ordinary weakness of the actual bridge end suffices for weakness of the
unchanged first attachment; all local geometry is constructed from the span. -/
theorem firstEnd_isWeakHomotopyEquivalence (hV : IsOpen V)
    (hweak : IsWeakHomotopyEquivalence d.normalized.i0.hom) :
    IsWeakHomotopyEquivalence d.normalized.firstEnd.hom :=
  d.normalized.firstEnd_isWeakHomotopyEquivalence d.bridgeTargetHeight
    d.bridgeTargetHeight_target 0 zero_lt_one hV
    (d.normalizedBridgeEndCollarSDR 0 zero_lt_one) hweak

end Quillen.NormalizedFibrationSpan.Data
