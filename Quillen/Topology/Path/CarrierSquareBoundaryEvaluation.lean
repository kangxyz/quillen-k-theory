/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.CarrierSquareBoundary

/-!
# Pointwise and continuous evaluation of exact carrier boundary cancellation

A full-square pointwise equality preserves the original collapse, boundary casts and the
entire two-half collapse/cancellation clock. Continuity is needed to map a square, but not
to compare two already supplied continuous squares by their full evaluation formulas.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Quillen.CarrierPathSquare
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {a₀ b₀ a₁ b₁ : X} {c₀ d₀ c₁ d₁ : Y}
  {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}
  {q₀ : Path c₀ d₀} {q₁ : Path c₁ d₁} {j : Path c₀ c₁} {k : Path d₀ d₁}

/-- Continuous evaluation sends the whole square and each literal edge to their mapped paths. -/
def Square.map (Q : Square p₀ p₁ l m) (f : C(X, Y)) :
    Square (p₀.map f.continuous) (p₁.map f.continuous)
      (l.map f.continuous) (m.map f.continuous) where
  parameter := f.comp Q.parameter
  at_zero s := congrArg f (Q.at_zero s)
  at_one s := congrArg f (Q.at_one s)
  left r := congrArg f (Q.left r)
  right r := congrArg f (Q.right r)

/-- Mapping does not change either interior coordinate of the original square. -/
theorem Square.map_apply (Q : Square p₀ p₁ l m) (f : C(X, Y)) (r s : unitInterval) :
    (Q.map f).parameter (r, s) = f (Q.parameter (r, s)) := rfl

/-- Full-square pointwise evaluation commutes with the original collapse at every coordinate. -/
theorem Square.toBoundary_natural (Q : Square p₀ p₁ l m) (S : Square q₀ q₁ j k)
    (f : X → Y) (h : ∀ r s, f (Q.parameter (r, s)) = S.parameter (r, s))
    (r s : unitInterval) : f (Q.toBoundary (r, s)) = S.toBoundary (r, s) :=
  h (ThreeSideSquare.collapse (r, s)).1 (ThreeSideSquare.collapse (r, s)).2

/-- All exact whole-boundary casts preserve the same pointwise interior comparison. -/
theorem Square.boundaryOfPaths_natural (Q : Square p₀ p₁ l m) (S : Square q₀ q₁ j k)
    (f : X → Y) (h : ∀ r s, f (Q.parameter (r, s)) = S.parameter (r, s))
    {p p' : Path a₀ b₀} {q q' : Path c₀ d₀}
    (hp : p₀ = p) (hp' : (l.trans p₁).trans m.symm = p')
    (hq : q₀ = q) (hq' : (j.trans q₁).trans k.symm = q') (r s : unitInterval) :
    f (Q.boundaryOfPaths hp hp' (r, s)) = S.boundaryOfPaths hq hq' (r, s) :=
  Q.toBoundary_natural S f h r s

/-- In particular the continuous-map boundary has exactly the mapped original interior. -/
theorem Square.map_toBoundary (Q : Square p₀ p₁ l m) (f : C(X, Y)) (r s : unitInterval) :
    (Q.map f).toBoundary (r, s) = f (Q.toBoundary (r, s)) := rfl

/-- Whole path pointwise equality survives the original terminal-pause cancellation clock. -/
theorem transRefl_natural {a b : X} {c d : Y} (p : Path a b) (q : Path c d)
    (f : X → Y) (h : ∀ s, f (p s) = q s) (r s : unitInterval) :
    f (Path.Homotopy.transRefl p (r, s)) = Path.Homotopy.transRefl q (r, s) :=
  h _

private theorem trans_natural {a b c : X} {d e g : Y}
    (p : Path a b) (q : Path b c) (p' : Path d e) (q' : Path e g)
    (f : X → Y) (hp : ∀ s, f (p s) = p' s) (hq : ∀ s, f (q s) = q' s)
    (s : unitInterval) : f ((p.trans q) s) = (p'.trans q') s := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

variable {a b c : X} {d e g : Y}
  {old : Path a c} {new : Path b c} {move : Path a b}
  {old' : Path d g} {new' : Path e g} {move' : Path d e}

/-- Full cone-square evaluation preserves both halves of collapse followed by pause removal. -/
theorem Square.coneBoundary_natural (Q : Square old new move (Path.refl c))
    (S : Square old' new' move' (Path.refl g)) (f : X → Y)
    (h : ∀ r s, f (Q.parameter (r, s)) = S.parameter (r, s)) (r s : unitInterval) :
    f (Q.coneBoundary (r, s)) = S.coneBoundary (r, s) := by
  have hm : ∀ t, f (move t) = move' t := fun t ↦
    (congrArg f (Q.left t)).symm.trans ((h t 0).trans (S.left t))
  have hn : ∀ t, f (new t) = new' t := fun t ↦
    (congrArg f (Q.at_one t)).symm.trans ((h 1 t).trans (S.at_one t))
  rw [Square.coneBoundary_apply, Square.coneBoundary_apply]
  split_ifs
  · exact h _ _
  · exact transRefl_natural (move.trans new) (move'.trans new') f
      (trans_natural move new move' new' f hm hn) _ s

/-- Continuous evaluators need only the same full-square equation; endpoints are not substitutes. -/
theorem Square.coneBoundary_continuous_natural (Q : Square old new move (Path.refl c))
    (S : Square old' new' move' (Path.refl g)) (f : C(X, Y))
    (h : ∀ r s, f (Q.parameter (r, s)) = S.parameter (r, s)) (r s : unitInterval) :
    f (Q.coneBoundary (r, s)) = S.coneBoundary (r, s) :=
  Q.coneBoundary_natural S f h r s

end Quillen.CarrierPathSquare
