/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyFiber.BasepointTransport
public import Quillen.Topology.HomotopyFiber.StrictWeakTransport
public import Quillen.Topology.HELP.TwoOfThree

/-! # Compact HELP on original fibers is preserved along individual paths

The genuine path transport equivalences and their strict original-map
naturality supply HELP composition/cancellation. Connectedness only chooses
one path for each individual conclusion, never a continuous path family.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Quillen.HomotopyFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)

/-- HELP for the actual source-change map propagates along a displayed base path. -/
theorem compactHELP_mapOver_of_path {b c : B} (γ : Path b c)
    (h : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty (mapOver p q f sq c) := by
  have hp := compactHELP_of_homotopyEquiv (basepointTransportEquiv p γ)
  have hq := compactHELP_of_homotopyEquiv (basepointTransportEquiv q γ)
  have hw := hq.comp h
  rw [basepointTransportEquiv_mapOver p q f sq γ] at hw
  exact hw.cancel_first hp

/-- The same propagation retains both maps of an arbitrary original square. -/
theorem compactHELP_map_of_path {B' : Type u} [TopologicalSpace B']
    (q' : C(F, B')) (v : C(B, B')) (sq' : v.comp p = q'.comp f)
    {b c : B} (γ : Path b c)
    (h : CompactHomotopyExtensionLiftingProperty (map f v sq' b)) :
    CompactHomotopyExtensionLiftingProperty (map f v sq' c) := by
  have hp := compactHELP_of_homotopyEquiv (basepointTransportEquiv p γ)
  have hq := compactHELP_of_homotopyEquiv (basepointTransportEquiv q' (γ.map v.continuous))
  have hw := hq.comp h
  rw [basepointTransportEquiv_map p q' f v sq' γ] at hw
  exact hw.cancel_first hp

/-- Only individual path-connectedness, not continuously chosen paths, is used. -/
theorem compactHELP_mapOver_of_joined {b c : B} (hbc : Joined b c)
    (h : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty (mapOver p q f sq c) := by
  obtain ⟨γ⟩ := hbc
  exact compactHELP_mapOver_of_path p q f sq γ h

end Quillen.HomotopyFiber

namespace Quillen.HomotopyFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
  (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
include hp hq

/-- For genuine fibrations, HELP for their original strict-fiber transition
is equivalent to HELP for their original path-space fiber transition. -/
theorem compactHELP_strictMapOver_iff (b : B) :
    CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b) ↔
      CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b) := by
  have hjp := compactHELP_of_homotopyEquiv (strictFiberHomotopyEquivOfLifting p hp b)
  have hjq := compactHELP_of_homotopyEquiv (strictFiberHomotopyEquivOfLifting q hq b)
  constructor
  · intro h
    have hw : CompactHomotopyExtensionLiftingProperty
        ((mapOver p q f sq b).comp (strictFiberInclusion p b)) := hjq.comp h
    exact hw.cancel_first hjp
  · intro h
    have hw : CompactHomotopyExtensionLiftingProperty
        ((strictFiberInclusion q b).comp (strictMapOver p q f sq b)) := h.comp hjp
    exact hw.cancel_second hjq

/-- Genuine strict-fiber HELP propagates along one actual path in the base. -/
theorem compactHELP_strictMapOver_of_joined {b c : B} (hbc : Joined b c)
    (h : CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq c) :=
  (compactHELP_strictMapOver_iff p q f sq hp hq c).2
    (compactHELP_mapOver_of_joined p q f sq hbc
      ((compactHELP_strictMapOver_iff p q f sq hp hq b).1 h))

end Quillen.HomotopyFiber
