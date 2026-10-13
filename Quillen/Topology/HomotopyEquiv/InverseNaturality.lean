/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Naturality of the actual inverses of homotopy equivalences

A homotopy-commutative square of forward maps determines an actual continuous
homotopy for the given inverses. The construction inserts the target left-inverse
homotopy, follows the supplied square, and removes the source right-inverse
homotopy. It makes no assertion for inverses of mere weak equivalences.
-/

@[expose] public section

noncomputable section

namespace ContinuousMap.HomotopyEquiv

universe u v w z

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Cancel the genuine forward homotopy equivalences in a square, retaining
both prescribed inverse maps and constructing a continuous homotopy between them. -/
def inverseNaturalityHomotopy (a : HomotopyEquiv X X') (b : HomotopyEquiv Y Y')
    (u : C(X, Y)) (v : C(X', Y'))
    (H : (b.toFun.comp u).Homotopy (v.comp a.toFun)) :
    (u.comp a.invFun).Homotopy (b.invFun.comp v) :=
  ((Classical.choice b.left_inv).symm.compContinuousMap (u.comp a.invFun)).trans
    (((ContinuousMap.Homotopy.refl b.invFun).comp
      (H.compContinuousMap a.invFun)).trans
        ((ContinuousMap.Homotopy.refl (b.invFun.comp v)).comp
          (Classical.choice a.right_inv)))

end ContinuousMap.HomotopyEquiv
