/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.HomotopyFiber.LoopPrefixUnitCoherence

/-! # Actual endpoint-fixed unit/associator coherence consumers -/
noncomputable section
open scoped Topology
open Quillen.HomotopyFiber
universe u v u' v'
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

example {a b c : Y} (p : Path a b) (q : Path b c) :
    (pathUnitRemoval (p.trans q)).Homotopic (pathAssociatorUnitRoute p q) :=
  ⟨pathUnitAssociatorHomotopy p q⟩

example {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) :
    (loopPrefixUnitPath f' (u x) (v y)
      ((H.evalAt x).symm.trans (γ.map v.continuous))).Homotopic
        (((loopPrefixHomotopySquare u v H x y γ).evalAt (Path.refl y)).trans
          ((loopPrefixUnitPath f x y γ).map (homotopySquareMap u v H y).continuous)) :=
  ⟨loopPrefixHomotopySquareUnitCoherence u v H x y γ⟩
