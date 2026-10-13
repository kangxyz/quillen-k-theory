/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HELP.CubicalLifting
public import Quillen.Topology.HELP.ContractibleTest

/-! # Original weak equivalences from genuine compact HELP on strict fibers

Both original projections have actual homotopy lifting. Their actual strict-fiber
maps have compact HELP. Contracted tests and the actual cubical representatives
then prove the original total map weak, without realization or CW assumptions.
-/
@[expose] public section

noncomputable section
open scoped Topology
universe u
namespace Quillen
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- The actual total map solves compact contracted strict tests from genuine
HLP of its original projections and compact HELP on all original strict fibers. -/
theorem contractedStrictHELP_of_fiberHELP
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b)) :
    ContractedStrictHELP f := by
  intro A D _ _ i hi d HD a b w
  exact strictHELP_on_contracted_test_of_all_fibers p q f sq hp hq hf A D i hi d HD a b w

/-- Complete weak equivalence of the original total map, including π₀ and
component surjectivity, with no realization model required for either total. -/
theorem isWeakHomotopyEquivalence_of_fiberHELP
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b, CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq b)) :
    IsWeakHomotopyEquivalence f :=
  (contractedStrictHELP_of_fiberHELP p q f sq hp hq hf).isWeakHomotopyEquivalence

end Quillen
