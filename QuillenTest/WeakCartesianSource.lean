/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyPullback.WeakCartesianSource

/-! Canonical comparison regression tests under weak change of total source. -/
@[expose] public section


noncomputable section
open Quillen Quillen.HomotopyPullback
open scoped Topology unitInterval
universe u

variable {X Y A B Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
  (p : C(X,B)) (q : C(Y,B)) (k : C(A,B))
  (r : C(Z,A)) (f : C(Z,X)) (g : C(Z,Y))
  (commP : p.comp f = k.comp r) (commQ : q.comp g = k.comp r)
  (e : C(X,Y)) (he : IsWeakHomotopyEquivalence e)
  (hover : q.comp e = p) (htriangle : e.comp f = g)
  (h : IsWeakHomotopyEquivalence (comparison q k r g commQ))

-- The original comparison, rather than a replacement square, has every
-- required based bijection, including n = 0.
example (z : Z) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (comparison p k r f commP) (x := z) rfl) :=
  (comparison_isWeakHomotopyEquivalence_of_sourceMap
    p q k r f g commP commQ e he hover htriangle h).homotopy_bijective z n

example [IsEmpty Z] : IsEmpty (HomotopyPullback p k) :=
  (comparison_isWeakHomotopyEquivalence_of_sourceMap
    p q k r f g commP commQ e he hover htriangle h).isEmpty_target

-- Source change retains the whole actual path and parameter even when e
-- is merely weak and no inverse of e was selected.
example (z : HomotopyPullback (q.comp e) k) :
    (sourceMap k q e z).val.1 = z.val.1 ∧
      ∀ t, (sourceMap k q e z).val.2.2 t = z.val.2.2 t :=
  ⟨rfl, fun _ ↦ rfl⟩
