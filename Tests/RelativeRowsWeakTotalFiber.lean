/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.RelativeRows.WeakTotalFiber
public import Quillen.Waldhausen.Fibration.AllWeak.TotalFiberSquare

/-! The unchanged relative-tail comparison, its whole constant path and chosen
zero, finite components, and both exact nested inputs used by global assembly. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Tests.RelativeRowsWeakTotalFiber
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open RelativeRows
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V)

example (n : SimplexCategory) : IsWeakHomotopyEquivalence (rowFiberInclusion N n) :=
  rowFiberInclusion_isWeakHomotopyEquivalence N n

example : IsWeakHomotopyEquivalence (totalTailFiberComparison N) :=
  totalTailFiberComparison_isWeakHomotopyEquivalence N

example (x : V.Delooping) : (totalTailFiberComparison N x).1.1 =
    SSet.toTop.map (totalFiberInclusion N) x := rfl

example (x : V.Delooping) : (totalTailFiberComparison N x).1.2 =
    ContinuousMap.const _ (ordinaryTotalBasepoint (acyclicStructure N)) := rfl

example : totalTailFiberComparison N V.kBasepoint =
    HomotopyFiber.basepoint (totalTailMap N) (ordinaryTotalBasepoint (acyclicStructure N))
      (totalBasepoint N) (totalTailMap_basepoint N) :=
  totalTailFiberComparison_basepoint N

example (x : V.Delooping) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (totalTailFiberComparison N) (x := x) rfl) :=
  totalTailFiberComparison_bijective N x 0

example : IsWeakHomotopyEquivalence
    (totalTailFiberComparison (AllWeak.nested (acyclicStructure N))) :=
  totalTailFiberComparison_isWeakHomotopyEquivalence (AllWeak.nested (acyclicStructure N))

example : (AllWeak.relativeTailFiberMap N).comp
      (totalTailFiberComparison (AllWeak.nested (acyclicStructure N))) =
    (totalTailFiberComparison N).comp (acyclicInclusionMap N) :=
  AllWeak.relativeTailFiberMap_totalTailFiberComparison N

end Tests.RelativeRowsWeakTotalFiber
