/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.EvaluationOperations
/-!
# Comparing two evaluations of the exact path associator

Local candidate for `Aglib.Topology.Path.AssociatorEvaluationComparison`.
For arbitrary topological spaces, an arbitrary source evaluation and a continuous target
evaluation, equality on three complete paths gives equality on their original associators.
The current consumer is the selected carrier-square correction naturality adapter.
Existing `Path.Evaluation.transAssoc` supplies each evaluation; this lemma compares both.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
namespace Path.Evaluation
variable {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
variable {a b c d e : X} {a' b' c' d' e' : Y}

/-- Comparing the literal associators through two evaluations retains the original clocks. -/
theorem associator_evaluations (f : X → T) (g : C(Y, T))
    (p : Path a b) (q : Path b c) (w : Path c d)
    (p' : Path a' b') (q' : Path b' c') (w' : Path c' d')
    (hp : ∀ s, f (p s) = g (p' s)) (hq : ∀ s, f (q s) = g (q' s))
    (hw : ∀ s, f (w s) = g (w' s)) (r s : I) :
    f (Path.Homotopy.transAssoc p q w (r, s)) =
      g (Path.Homotopy.transAssoc p' q' w' (r, s)) := by
  exact (Path.Evaluation.transAssoc f p q w
    (p'.map g.continuous) (q'.map g.continuous) (w'.map g.continuous)
    hp hq hw r s).trans
      (Path.Evaluation.transAssoc g p' q' w'
        (p'.map g.continuous) (q'.map g.continuous) (w'.map g.continuous)
        (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) r s).symm

end Path.Evaluation
