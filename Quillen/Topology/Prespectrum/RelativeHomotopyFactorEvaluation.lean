/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction
public import Quillen.Topology.Prespectrum.RelativeHomotopyOperationEvaluation

/-! Whole native factors extracted before specializing the ambient topology. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.NativeFactorEvaluation
open LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {a b c : X}
  {E F : LoopPrespectrum.{u}} {f g k : E ⟶ F}
  (n : ℕ) (x : E.space n) (ev : X → F.space n)

/-- Whole first-factor evaluation under one fixed native target topology. -/
theorem left_factor (p : Path a b) (q : Path b c)
    (H : Homotopy f g) (K : Homotopy g k)
    (h : ∀ t, ev ((p.trans q) t) = (H.trans K).level n (t, x)) (s : I) :
    ev (p s) = H.level n (s, x) := by
  change ev (p s) = H.path n x s
  apply Path.Evaluation.left_factor ev p q (H.path n x) (K.path n x)
  intro t
  rw [← Homotopy.path_trans]
  exact h t

/-- Whole second-factor evaluation retains the original midpoint and half cut. -/
theorem right_factor (p : Path a b) (q : Path b c)
    (H : Homotopy f g) (K : Homotopy g k)
    (h : ∀ t, ev ((p.trans q) t) = (H.trans K).level n (t, x)) (s : I) :
    ev (q s) = K.level n (s, x) := by
  change ev (q s) = K.path n x s
  apply Path.Evaluation.right_factor ev p q (H.path n x) (K.path n x)
  intro t
  rw [← Homotopy.path_trans]
  exact h t

/-- The full source boundary supplies the first factor without any concrete path conversion. -/
theorem comparison_source_left (p : Path a b) (q : Path b c) (w : Path a c)
    (H : Homotopy f g) (K : Homotopy g k) (W : Homotopy f k)
    (J : (p.trans q).Homotopy w) (JN : (H.trans K).RelHomotopy W)
    (h : ∀ r t, ev (J (r, t)) = JN.level n (r, (t, x))) (s : I) :
    ev (p s) = H.level n (s, x) := by
  apply left_factor n x ev p q H K
  intro t
  exact (congrArg ev (J.map_zero_left t)).symm.trans
    ((h 0 t).trans ((JN.level n).apply_zero (t, x)))

/-- The full target boundary supplies the second factor with all native parameters fixed. -/
theorem comparison_target_right (p : Path a b) (q : Path b c) (w : Path a c)
    (H : Homotopy f g) (K : Homotopy g k) (W : Homotopy f k)
    (J : w.Homotopy (p.trans q)) (JN : W.RelHomotopy (H.trans K))
    (h : ∀ r t, ev (J (r, t)) = JN.level n (r, (t, x))) (s : I) :
    ev (q s) = K.level n (s, x) := by
  apply right_factor n x ev p q H K
  intro t
  exact (congrArg ev (J.map_one_left t)).symm.trans
    ((h 1 t).trans ((JN.level n).apply_one (t, x)))

end Quillen.NativeFactorEvaluation
