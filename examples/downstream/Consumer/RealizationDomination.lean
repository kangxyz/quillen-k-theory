/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.Domination

/-!
# Whitehead recognition for an actual product with a contractible space

The target is the literal product of a realization and an arbitrary space
with a displayed contraction. The product is not assumed to be a realization
or to carry a homotopy equivalence from one. Its explicit projection, section,
and contraction construct the domination needed to invert any specified weak
map into it. Both inverse homotopies concern that unchanged map.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen
open scoped Simplicial Topology unitInterval

universe u
namespace Consumer.RealizationDomination

variable {X T : SSet.{u}} {Z : Type u} [TopologicalSpace Z]

/-- Any original weak map to this actual product admits a genuine inverse. -/
def productHomotopyEquiv (z : Z)
    (K : (ContinuousMap.const Z z).Homotopy (ContinuousMap.id Z))
    (f : C(|X|, |T| × Z)) (hf : IsWeakHomotopyEquivalence f) :
    ContinuousMap.HomotopyEquiv |X| (|T| × Z) := by
  let a : C(|T| × Z, |T|) := ContinuousMap.fst
  let b : C(|T|, |T| × Z) := ⟨fun x ↦ (x, z), by fun_prop⟩
  let H : (b.comp a).Homotopy (ContinuousMap.id (|T| × Z)) := {
    toFun p := (p.2.1, K (p.1, p.2.2))
    continuous_toFun := by fun_prop
    map_zero_left p := Prod.ext rfl (K.apply_zero p.2)
    map_one_left p := Prod.ext rfl (K.apply_one p.2) }
  exact Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination f hf T a b H

/-- The construction retains an arbitrary prescribed original forward map. -/
theorem productHomotopyEquiv_toFun (z : Z)
    (K : (ContinuousMap.const Z z).Homotopy (ContinuousMap.id Z))
    (f : C(|X|, |T| × Z)) (hf : IsWeakHomotopyEquivalence f) :
    (productHomotopyEquiv z K f hf).toFun = f := rfl

/-- The target-side homotopy remains a homotopy on the original product. -/
def productRightInverseHomotopy (z : Z)
    (K : (ContinuousMap.const Z z).Homotopy (ContinuousMap.id Z))
    (f : C(|X|, |T| × Z)) (hf : IsWeakHomotopyEquivalence f) :
    (f.comp (productHomotopyEquiv z K f hf).invFun).Homotopy
      (ContinuousMap.id (|T| × Z)) :=
  (productHomotopyEquiv z K f hf).right_inv.some

/-- The source-side homotopy also concerns the unchanged original map. -/
def productLeftInverseHomotopy (z : Z)
    (K : (ContinuousMap.const Z z).Homotopy (ContinuousMap.id Z))
    (f : C(|X|, |T| × Z)) (hf : IsWeakHomotopyEquivalence f) :
    ((productHomotopyEquiv z K f hf).invFun.comp f).Homotopy (ContinuousMap.id |X|) :=
  (productHomotopyEquiv z K f hf).left_inv.some

end Consumer.RealizationDomination
