/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyFiber.CartesianDetection
public import Quillen.Topology.HomotopyPullback.Symmetry
public import Quillen.Topology.HomotopyPullback.CartesianTransport

/-! # Genuine homotopy equivalence of the original fibers of an equivalence square

Both supplied total and base maps are genuine homotopy equivalences. Cancel
the actual source projection of their homotopy pullback to obtain a genuine
comparison equivalence. Source invariance and the explicit prefix/suffix
comparison-fiber homotopy then give a genuine equivalence with exactly the
original fiber map as its forward map. No weak-to-strong upgrade is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Quillen
namespace HomotopyPullback
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]

/-- Genuine total and base equivalences make the original constant-path
comparison a genuine homotopy equivalence. -/
def comparisonHomotopyEquivOfEquivalences
    (p : C(X, A)) (q : C(Y, B))
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) :
    ContinuousMap.HomotopyEquiv X (HomotopyPullback q eb.toFun) :=
  Quillen.homotopyEquivCancelRight
    (a := comparison q eb.toFun p e.toFun sq.symm)
    (sourceProjectionEquivOfParameterEquiv q eb.toFun eb rfl) rfl e rfl

@[simp] theorem comparisonHomotopyEquivOfEquivalences_toFun
    (p : C(X, A)) (q : C(Y, B))
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) :
    (comparisonHomotopyEquivOfEquivalences p q e eb sq).toFun =
      comparison q eb.toFun p e.toFun sq.symm := rfl

/-- The actual comparison induces a genuine equivalence on the original
fibers over the unchanged parameter base, retaining the entire outer path. -/
def comparisonFiberHomotopyEquivOfEquivalences
    (p : C(X, A)) (q : C(Y, B))
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) (a : A) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber p a)
      (HomotopyFiber (baseProjection q eb.toFun) a) :=
  HomotopyFiber.sourceEquiv (baseProjection q eb.toFun)
    (comparisonHomotopyEquivOfEquivalences p q e eb sq) a

@[simp] theorem comparisonFiberHomotopyEquivOfEquivalences_toFun
    (p : C(X, A)) (q : C(Y, B))
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) (a : A) :
    (comparisonFiberHomotopyEquivOfEquivalences p q e eb sq a).toFun =
      comparisonFiber p q e.toFun eb.toFun sq.symm a := rfl

end HomotopyPullback
namespace HomotopyFiber
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X, A)} {q : C(Y, B)}

/-- The original fiber map of a strictly commuting square of genuine total
and base homotopy equivalences is itself a genuine homotopy equivalence. -/
def mapHomotopyEquivOfEquivalences
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) (a : A) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber p a) (HomotopyFiber q (eb a)) := by
  let ef := HomotopyPullback.comparisonFiberHomotopyEquivOfEquivalences p q e eb sq a
  let eg := HomotopyPullback.baseFiberHomotopyEquiv q eb.toFun a
  let h : (eg.toFun.comp (map e.toFun eb.toFun sq a)).Homotopic ef.toFun :=
    ⟨(HomotopyPullback.comparisonFiberHomotopy p q e.toFun eb.toFun sq.symm a).symm⟩
  let ec := replaceForward ef (eg.toFun.comp (map e.toFun eb.toFun sq a)) h
  exact Quillen.homotopyEquivCancelRight eg rfl ec rfl

/-- The prescribed original forward map is retained definitionally. -/
@[simp] theorem mapHomotopyEquivOfEquivalences_toFun
    (e : ContinuousMap.HomotopyEquiv X Y) (eb : ContinuousMap.HomotopyEquiv A B)
    (sq : eb.toFun.comp p = q.comp e.toFun) (a : A) :
    (mapHomotopyEquivOfEquivalences e eb sq a).toFun = map e.toFun eb.toFun sq a := rfl

end HomotopyFiber
end Quillen
