/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Prespectrum.ParameterLoopingWeakEquivalence

/-! # Consumers of complete weak invariance of the original loop maps

The tests use arbitrary loops, including nonconstant components, and iterate
the original parameter-correct looping without connectivity assumptions.
-/
@[expose] public section

noncomputable section
open CategoryTheory Quillen
universe u
namespace Quillen.Tests.LoopWeakEquivalence

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (hf : IsWeakHomotopyEquivalence f)
include hf

/-- Every target loop component is represented by an actual postcomposed source loop. -/
theorem represents_target_loop_component (δ : Path y y) :
    ∃ γ : Path x x, Joined (basedLoopMap f h γ) δ :=
  (basedLoopMap_isWeakHomotopyEquivalence f h hf).component_surjective δ

/-- Equality of arbitrary loop components is reflected, not just the constant component. -/
theorem reflects_loop_components (γ δ : Path x x)
    (hγδ : Joined (basedLoopMap f h γ) (basedLoopMap f h δ)) : Joined γ δ :=
  joined_of_homotopyGroupMap_zero_injective (basedLoopMap f h) γ δ
    ((basedLoopMap_isWeakHomotopyEquivalence f h hf).homotopy_bijective γ 0).injective hγδ

/-- The induced higher maps are bijective at any chosen loop, with no joining path
from that loop to the constant loop supplied. -/
theorem bijective_at_arbitrary_loop (γ : Path x x) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (basedLoopMap f h) (x := γ) rfl) :=
  (basedLoopMap_isWeakHomotopyEquivalence f h hf).homotopy_bijective γ n

omit hf
open LoopPrespectrum

/-- The complete result can be iterated on the unchanged loop-space objects,
then used by the actual positive-level stable-equivalence criterion. -/
theorem double_parameter_looping_isStableEquivalence
    {E F : LoopPrespectrum.{u}} (g : E ⟶ F)
    (hg : ∀ n, IsWeakHomotopyEquivalence (g.map (n + 1))) :
    IsStableEquivalence (parameterLoopingMap (parameterLoopingMap g)) :=
  parameterLoopingMap_isStableEquivalence_of_positiveLevel (parameterLoopingMap g)
    (parameterLoopingMap_positiveLevel_isWeakHomotopyEquivalence g hg)

end Quillen.Tests.LoopWeakEquivalence
