/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.DisplayedComparisonRecognition

/-! # Independent displayed-comparison algebra and original-chain client -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Quillen.Consumer.N4Cancellation
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Both conclusions concern the supplied original comparison and arbitrary target systems. -/
theorem displayedOriginalComparison (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z))
    (H : (k.comp f).Homotopy g) {x : X} {y : Y} {z : Z}
    (γ : Path (f x) y) (δ : Path (g x) z) (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N) :
    Function.Bijective (piMap 0 k (x := y) rfl) ∧
      ∀ V : LocalCoefficients.System.{u, u} Z,
        QuasiIso (LocalCoefficients.UniverseLift.chainMap k V) :=
  ⟨IsPlusConstruction.displayedComparison_piOne_bijective f g k H γ δ N hf hg,
    IsPlusConstruction.displayedComparison_twisted_quasiIso f g k H γ δ N hf hg⟩

end Quillen.Consumer.N4Cancellation
