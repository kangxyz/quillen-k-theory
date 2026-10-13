/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.DisplayedComparisonRecognition
public import Quillen.Topology.Realization.Whitehead

/-!
# An actual inverse to a displayed comparison between realizations

Actual simplicial realizations, the displayed under-source comparison and its
homotopy, and supplied geometric covering data are retained. The resulting
homotopy equivalence has exactly that supplied comparison as its forward map.
No comparison existence, homotopy-class uniqueness, or general classical CW
recognition theorem is asserted.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped Simplicial
universe u

namespace Quillen.IsPlusConstruction
variable {X : Type u} [TopologicalSpace X] {Y Z : SSet.{u}}

/-- Recognize the supplied comparison itself as an actual homotopy equivalence
for actual realization targets and supplied simply connected covers. -/
def displayedComparisonHomotopyEquivSuppliedCovers
    (f : C(X, |Y|)) (g : C(X, |Z|)) (k : C(|Y|, |Z|)) (H : (k.comp f).Homotopy g)
    {x : X} {y : |Y|} {z : |Z|} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → |Y|} {q : F → |Z|} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (lift : C(E, F)) (hlift : ∀ e, q (lift e) = k (p e)) (e₀ : E) :
    ContinuousMap.HomotopyEquiv |Y| |Z| :=
  Realization.homotopyEquivOfWeakHomotopyEquivalence k
    (displayedComparison_isWeakHomotopyEquivalence_suppliedCovers
      f g k H γ δ N hf hg hp hq lift hlift e₀)

/-- The forward map of the constructed inverse data is the original displayed comparison. -/
@[simp] theorem displayedComparisonHomotopyEquivSuppliedCovers_toFun
    (f : C(X, |Y|)) (g : C(X, |Z|)) (k : C(|Y|, |Z|)) (H : (k.comp f).Homotopy g)
    {x : X} {y : |Y|} {z : |Z|} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → |Y|} {q : F → |Z|} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (lift : C(E, F)) (hlift : ∀ e, q (lift e) = k (p e)) (e₀ : E) :
    (displayedComparisonHomotopyEquivSuppliedCovers
      f g k H γ δ N hf hg hp hq lift hlift e₀).toFun = k := rfl

end Quillen.IsPlusConstruction
