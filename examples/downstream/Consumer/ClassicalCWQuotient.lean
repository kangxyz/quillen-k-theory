/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.CharacteristicQuotient
public import Mathlib.Topology.Homotopy.Basic

/-! Actual maps and homotopies assembled on the original classical-CW subtype. -/
@[expose] public section
noncomputable section
open Set Topology
open scoped unitInterval
universe u v
namespace Consumer.ClassicalCWQuotient
open Quillen.ClassicalCW
variable {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {Y : Type v} [TopologicalSpace Y]

/-- A function with continuous characteristic restrictions gives the literal continuous map. -/
def mapOfDisks (f : C → Y)
    (hf : ∀ n (i : RelCWComplex.cell C n),
      Continuous (fun z : CharacteristicDisk n => f (characteristicQuotient C ⟨n, i, z⟩))) :
    C(C, Y) := ⟨f, (continuous_iff_characteristic C f).mpr hf⟩

/-- Cellwise product continuity and the prescribed endpoint equations give an actual homotopy. -/
def homotopyOfDisks (f g : C(C, Y)) (H : I × C → Y)
    (hH : Continuous (fun z : I × CharacteristicDomain C =>
      H (z.1, characteristicQuotient C z.2)))
    (h0 : ∀ x, H (0, x) = f x) (h1 : ∀ x, H (1, x) = g x) :
    ContinuousMap.Homotopy f g where
  toFun := H
  continuous_toFun := continuous_homotopy_of_characteristic C H hH
  map_zero_left := h0
  map_one_left := h1

/-- Homotopy assembly preserves the given function pointwise, not just its class. -/
theorem homotopyOfDisks_apply (f g : C(C, Y)) (H : I × C → Y)
    (hH : Continuous (fun z : I × CharacteristicDomain C =>
      H (z.1, characteristicQuotient C z.2)))
    (h0 : ∀ x, H (0, x) = f x) (h1 : ∀ x, H (1, x) = g x) (z : I × C) :
    homotopyOfDisks C f g H hH h0 h1 z = H z := rfl

end Consumer.ClassicalCWQuotient
