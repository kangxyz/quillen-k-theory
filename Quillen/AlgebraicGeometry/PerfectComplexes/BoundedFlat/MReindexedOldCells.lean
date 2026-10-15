/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeSupportOrders

/-! Exact transfer of the unchanged H0, chart, and bottom faces through their actual support. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) {k : ℕ}
  (N : Fin (k + 1) → BassOverlap.Node P u v)
  (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))
  (hn : ∀ i, N (g i) = BassH1Merged.nodes P u v i)

/-- The common diagram uses full original model nodes and their actual common reference. -/
def nativeSimplex := ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
  (fun i ↦ (N i).1) (fun i ↦ (N i).2)

include hn in
/-- Whole native values are retained on each actual composed old support face. -/
theorem old_face_value {r d : ℕ} (b : Fin (r + 1) → Fin 131) (α : ⦋d⦌ ⟶ ⦋r⦌)
    (hb : Monotone (b ∘ α.toOrderHom)) (hgb : Monotone (g ∘ b ∘ α.toOrderHom))
    (n : ℕ) (z : StdSimplex ℝ (Fin (d + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (StdSimplex.map b (StdSimplex.map α.toOrderHom z)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (StdSimplex.map b (StdSimplex.map α.toOrderHom z), x) :=
  composed_supported_value (BassOverlap.commonReference P u v) (BassH1Merged.nodes P u v)
    N g hn b α hb hgb n z x

variable (o : SupportOrders f g)
include hn o in
/-- Every original positive chart value is retained, including its complete terminal pause. -/
theorem old_plus_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.plusParameter (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.plusParameter (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.oldIndex
      (BassSupportOrder.plusParameter (r, t))), x) = _
  obtain ⟨i, z, hz⟩ := BassH1Support.old_plus_support (r, t)
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.plusParameter (r, t)), x)
  rw [← hz]
  exact old_face_value P u v N g hn BassH1Order.oldIndex (BassSupportOrder.oldPlusFace i)
    (BassH1Order.oldPlus_monotone i) (o.oldPlus i) n z x

include hn o in
/-- The separate original inverse chart retains every native value and its literal pause. -/
theorem old_minus_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.minusParameter (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.minusParameter (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.oldIndex
      (BassSupportOrder.minusParameter (r, t))), x) = _
  obtain ⟨i, z, hz⟩ := BassH1Support.old_minus_support (r, t)
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.minusParameter (r, t)), x)
  rw [← hz]
  exact old_face_value P u v N g hn BassH1Order.oldIndex (BassSupportOrder.oldMinusFace i)
    (BassH1Order.oldMinus_monotone i) (o.oldMinus i) n z x

include hn o in
/-- The entire original bottom product family retains both independent scalar variables. -/
theorem old_bottom_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.bottomParameter.{u} (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.bottomParameter.{u} (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.oldIndex
      (BassSupportOrder.bottomParameter.{u} (r, t))), x) = _
  obtain ⟨z, hz⟩ := BassH1Support.old_bottom_support.{u} (r, t)
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.bottomParameter.{u} (r, t)), x)
  rw [← hz]
  exact old_face_value P u v N g hn BassH1Order.oldIndex BassSupportOrder.bottomFace
    BassH1Order.oldBottom_monotone o.oldBottom n z x

include hn o in
/-- Every point of the unchanged whole H0 surface retains its actual original native value. -/
theorem old_h0_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.h0Parameter (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.h0Parameter (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.oldIndex
      (BassSupportOrder.h0Parameter (r, t))), x) = _
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.h0Parameter (r, t)), x)
  rcases BassH1Support.old_h0_support (r, t) with ⟨i, z, hz⟩ | ⟨i, z, hz⟩
  · rw [← hz]
    exact old_face_value P u v N g hn BassH1Order.oldIndex (BassSupportOrder.h0PlusFace i)
      (BassH1Order.oldH0Plus_monotone i) (o.oldH0Plus i) n z x
  · rw [← hz]
    exact old_face_value P u v N g hn BassH1Order.oldIndex (BassSupportOrder.h0MinusFace i)
      (BassH1Order.oldH0Minus_monotone i) (o.oldH0Minus i) n z x

end Quillen.PerfectComplexes.BassMFamilyTransfer
