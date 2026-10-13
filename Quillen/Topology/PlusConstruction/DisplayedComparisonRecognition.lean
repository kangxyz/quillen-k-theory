/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.DisplayedComparisonFundamentalGroup
public import Quillen.Topology.LocalCoefficients.MapCancellation
public import Quillen.Topology.LocalCoefficients.TwistedWhiteheadSuppliedCovers

/-!
# Recognition of a displayed plus comparison with supplied covers

The comparison map, its under-source homotopy, and a commuting lift between
supplied simply connected covers are all explicit inputs. Its Pi one and
original twisted-chain hypotheses are derived from the two plus certificates,
then the genuine supplied-cover twisted Whitehead theorem applies.

This is recognition of an already displayed comparison, not construction or
uniqueness of a comparison. All spaces and coefficients share universe u.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace Quillen.IsPlusConstruction
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The supplied comparison preserves every original target local system,
by actual homotopy-factorization cancellation of the two given plus maps. -/
theorem displayedComparison_twisted_quasiIso
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    (A : LocalCoefficients.System.{u, u} Z) :
    QuasiIso (LocalCoefficients.UniverseLift.chainMap.{u, u, u} k A) :=
  LocalCoefficients.universeLift_quasiIso_of_displayed_factorization f g k H A
    (hf.localCoefficients (LocalCoefficients.pullback k A)) (hg.localCoefficients A)

/-- An already displayed comparison and under-source homotopy yield an actual
weak equivalence when actual simply connected covers and a commuting lift are supplied. -/
theorem displayedComparison_isWeakHomotopyEquivalence_suppliedCovers
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → Y} {q : F → Z} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (lift : C(E, F)) (hlift : ∀ e, q (lift e) = k (p e)) (e₀ : E) :
    IsWeakHomotopyEquivalence k := by
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  have hy := IsPlusConstruction.displayedComparison_piOne_bijective f g k H γ δ N hf hg
  have hπ : Function.Bijective (piMap 0 k (x := p e₀) rfl) :=
    homotopyGroupMap_bijective_at_all_points k y 1 hy (p e₀)
  exact LocalCoefficients.isWeakHomotopyEquivalence_of_twisted_quasiIso_suppliedCovers
    hp hq lift k hlift e₀ hπ
      (displayedComparison_twisted_quasiIso f g k H γ δ N hf hg)

end Quillen.IsPlusConstruction
