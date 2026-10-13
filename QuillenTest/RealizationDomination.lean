/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Realization.Domination

/-! # Realization domination constructs original inverse maps and homotopies -/

noncomputable section

open CategoryTheory Quillen
open scoped Simplicial Topology unitInterval

universe u

-- Domination supplies a strict section over the original target, even when
-- the source itself is not known to have any CW or realization type.
example {E Y : Type u} [TopologicalSpace E] [TopologicalSpace Y]
    (f : C(E, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) (y : Y) :
    MappingPath.endpoint f
      (Realization.mappingPathSectionOfDomination f hf T a b H y) = y :=
  ContinuousMap.congr_fun
    (Realization.mappingPathSectionOfDomination_endpoint f hf T a b H) y

-- The new target hypothesis is a displayed one-sided domination, rather
-- than an equivalence or an assumed inverse to this weak map.
example {X : SSet.{u}} {Y : Type u} [TopologicalSpace Y]
    (f : C(|X|, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) :
    ∃ g : C(Y, |X|), Nonempty ((g.comp f).Homotopy (ContinuousMap.id |X|)) ∧
      Nonempty ((f.comp g).Homotopy (ContinuousMap.id Y)) := by
  let e := Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination f hf T a b H
  exact ⟨e.invFun, e.left_inv, e.right_inv⟩

example {X : SSet.{u}} {Y : Type u} [TopologicalSpace Y]
    (f : C(|X|, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) :
    (Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination f hf T a b H).toFun = f :=
  rfl
