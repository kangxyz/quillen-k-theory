/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Topology.Prespectrum.TripleOperationEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexParameterPaths

/-! The literal split-triple evaluation algebra, before specializing any geometric endpoint. -/
@[expose] public section
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v
namespace Quillen

theorem scalar_triple_evaluation {Z : Type v} [TopologicalSpace Z]
    {E F : LoopPrespectrum.{u}} {a b c d : Z}
    {p₀ p₀' : Path a b} {p₁ p₁' : Path b c}
    {q₀ q₀' : Path a d} {q₁ q₁' : Path d c}
    {f g h f' g' h' : E ⟶ F}
    {H₀ H₀' : Homotopy f g} {H₁ H₁' : Homotopy g h}
    {K₀ K₀' : Homotopy f' g'} {K₁ K₁' : Homotopy g' h'}
    (n : ℕ) (ev : Z → E.space n → F.space n)
    (JA : p₀.Homotopy p₀') (JB : p₁.Homotopy p₁')
    (JM : (p₀.trans p₁).Homotopy (q₀.trans q₁))
    (JR : q₀.Homotopy q₀') (JS : q₁.Homotopy q₁')
    (hf : f' = f) (hh : h' = h)
    (A : H₀.RelHomotopy H₀') (B : H₁.RelHomotopy H₁')
    (R : K₀.RelHomotopy K₀') (S : K₁.RelHomotopy K₁')
    (M : (H₀.trans H₁).RelHomotopy ((K₀.trans K₁).cast hf hh))
    (eA : ∀ r s x, ev (JA (r, s)) x = A.level n (r, (s, x)))
    (eB : ∀ r s x, ev (JB (r, s)) x = B.level n (r, (s, x)))
    (eM : ∀ r s x, ev (JM (r, s)) x = M.level n (r, (s, x)))
    (eR : ∀ r s x, ev (JR (r, s)) x = R.level n (r, (s, x)))
    (eS : ∀ r s x, ev (JS (r, s)) x = S.level n (r, (s, x)))
    (r s : unitInterval) (x : E.space n) :
    ev (((JA.hcomp JB).symm.trans (JM.trans (JR.hcomp JS))) (r, s)) x =
      ((A.hcomp B).symm.trans (M.trans ((R.hcomp S).cast hf hh))).level n (r, (s, x)) := by
  rw [Path.Homotopy.trans_apply, Homotopy.RelHomotopy.level_trans_apply]
  split
  · rw [Homotopy.RelHomotopy.level_symm_apply]
    change ev ((JA.hcomp JB) (_, s)) x = _
    rw [Path.Homotopy.hcomp_apply, Homotopy.RelHomotopy.level_hcomp_apply]
    split
    · exact eA _ _ x
    · exact eB _ _ x
  · rw [Path.Homotopy.trans_apply, Homotopy.RelHomotopy.level_trans_apply]
    split
    · exact eM _ s x
    · rw [Homotopy.RelHomotopy.level_cast_apply, Path.Homotopy.hcomp_apply,
        Homotopy.RelHomotopy.level_hcomp_apply]
      split
      · exact eR _ _ x
      · exact eS _ _ x
end Quillen
