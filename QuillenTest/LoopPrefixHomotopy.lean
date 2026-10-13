/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.HomotopyFiber.LoopPrefixHomotopy

/-! # Original square tracks, at independent universes -/
noncomputable section
open scoped Topology
open Quillen Quillen.HomotopyFiber
universe u v u' v'
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']
  {f : C(X, Y)} {f' : C(X', Y')}

example (u : C(X, X')) (v : C(Y, Y'))
    (H : (v.comp f).Homotopy (f'.comp u)) (x : X) (y : Y)
    (γ : Path (f x) y) (t : unitInterval) :
    (loopPrefixHomotopySquare u v H x y γ (t, Path.refl y)).val.2 =
      ((Path.Homotopy.transAssoc (H.evalAt x).symm (γ.map v.continuous)
        (Path.refl (v y))).eval t).toContinuousMap := rfl

example (u : C(X, X')) (v : C(Y, Y'))
    (H : (v.comp f).Homotopy (f'.comp u)) (y : Y) (z : HomotopyFiber f y) :
    (homotopySquareMap u v H y z).val.2 =
      ((H.evalAt z.val.1).symm.trans ((toPath f y z).map v.continuous)).toContinuousMap :=
  homotopySquareMap_path u v H y z
