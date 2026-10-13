/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.Whitehead

/-!
# An actual inverse and its pointwise paths for a weak realization equivalence

This independent client extracts a continuous inverse and both continuous
inverse homotopies for the original map between actual simplicial realizations.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen
open scoped Simplicial Topology unitInterval

universe u
namespace Consumer.RealizationWhitehead

/-- The forward map of the constructed equivalence is literally the given map. -/
theorem original_forward_map {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) :
    (Realization.homotopyEquivOfWeakHomotopyEquivalence f hf).toFun = f := rfl

/-- An actual continuous inverse, rather than only inverse maps on homotopy groups. -/
def inverse {X Y : SSet.{u}} (f : C(|X|, |Y|)) (hf : IsWeakHomotopyEquivalence f) :
    C(|Y|, |X|) :=
  (Realization.homotopyEquivOfWeakHomotopyEquivalence f hf).invFun

/-- The inverse composite is homotopic to the identity on the original source. -/
def leftInverseHomotopy {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) :
    ((inverse f hf).comp f).Homotopy (ContinuousMap.id |X|) :=
  Classical.choice (Realization.homotopyEquivOfWeakHomotopyEquivalence f hf).left_inv

/-- The other inverse homotopy has the original target as its codomain. -/
def rightInverseHomotopy {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) :
    (f.comp (inverse f hf)).Homotopy (ContinuousMap.id |Y|) :=
  Classical.choice (Realization.homotopyEquivOfWeakHomotopyEquivalence f hf).right_inv

/-- Every source point has an actual path from its inverse composite to itself. -/
def leftInversePath {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) (x : |X|) : Path (inverse f hf (f x)) x :=
  (leftInverseHomotopy f hf).evalAt x

/-- Every target point has the corresponding actual right-inverse path. -/
def rightInversePath {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : IsWeakHomotopyEquivalence f) (y : |Y|) : Path (f (inverse f hf y)) y :=
  (rightInverseHomotopy f hf).evalAt y

end Consumer.RealizationWhitehead
