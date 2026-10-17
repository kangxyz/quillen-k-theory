/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.RetypedConeNullComparison
public import Quillen.Aglib.Topology.Path.EvaluationOperations

/-!
# Evaluation of the prescribed positive null words

The shared literal path operations come from `Path.Evaluation` in
`Quillen.Aglib.Topology.Path.EvaluationOperations`. This module retains the selected
straightening and pasted-null comparisons and their specialized evaluation proofs.
The evaluation function is arbitrary; neither comparison nor path time is changed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Path.Evaluation
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {a b c d e t : X} {a' b' c' d' e' t' : Y}

/-- A constant comparison retains the complete supplied path. -/
theorem comparison_refl (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.refl p (r, s)) = Path.Homotopy.refl p' (r, s) := hp s

/-- The inverse-pair contraction retains its actual scalar formula. -/
theorem reflTransSymm (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.reflTransSymm p (r, s)) =
      Path.Homotopy.reflTransSymm p' (r, s) := hp _

/-- Initial-pause cancellation retains its actual reversed terminal-pause formula. -/
theorem reflTrans (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.reflTrans p (r, s)) = Path.Homotopy.reflTrans p' (r, s) := hp _

/-- Boundary casts change only proofs, never either interior coordinate. -/
theorem comparison_cast (f : X → Y) {p q v w : Path a b} {p' q' v' w' : Path a' b'}
    (J : p.Homotopy q) (J' : p'.Homotopy q')
    (hp : p = v) (hq : q = w) (hp' : p' = v') (hq' : q' = w')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s)) (r s : I) :
    f (J.cast hp hq (r, s)) = J'.cast hp' hq' (r, s) := hJ r s

/-- The five-stage straightening word keeps every original comparison and path cut. -/
theorem straightPositiveWord (f : X → Y)
    (A : Path a b) (B : Path b c) (Q : Path c d) (L : Path a e) (F : Path e d)
    (A' : Path a' b') (B' : Path b' c') (Q' : Path c' d')
    (L' : Path a' e') (F' : Path e' d')
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F)))
    (J' : (B'.trans Q').Homotopy (A'.symm.trans (L'.trans F')))
    (hA : ∀ s, f (A s) = A' s) (hB : ∀ s, f (B s) = B' s)
    (hQ : ∀ s, f (Q s) = Q' s) (hL : ∀ s, f (L s) = L' s)
    (hF : ∀ s, f (F s) = F' s)
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s)) (r s : I) :
    f (Path.Homotopy.straightPositiveWord A B Q L F J (r, s)) =
      Path.Homotopy.straightPositiveWord A' B' Q' L' F' J' (r, s) := by
  have hT := path_trans f L F L' F' hL hF
  exact comparison_trans f _ _ _ _ (transAssoc f A B Q A' B' Q' hA hB hQ)
    (comparison_trans f _ _ _ _
      (comparison_hcomp f _ _ _ _ (comparison_refl f A A' hA) hJ)
      (comparison_trans f _ _ _ _
        (comparison_symm f _ _
          (transAssoc f A A.symm (L.trans F) A' A'.symm (L'.trans F')
            hA (path_symm f A A' hA) hT))
        (comparison_trans f _ _ _ _
          (comparison_hcomp f _ _ _ _
            (comparison_symm f _ _ (reflTransSymm f A A' hA))
            (comparison_refl f (L.trans F) (L'.trans F') hT))
          (reflTrans f (L.trans F) (L'.trans F') hT)))) r s

/-- The complete pasted-null word preserves its five nested comparison stages. -/
theorem pastedPositiveNullWord (f : X → Y)
    (A : Path a b) (B : Path b c) (Q : Path c d) (L : Path a e) (F : Path e d)
    (E : Path c t) (G : Path d t)
    (A' : Path a' b') (B' : Path b' c') (Q' : Path c' d')
    (L' : Path a' e') (F' : Path e' d') (E' : Path c' t') (G' : Path d' t')
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F)))
    (J' : (B'.trans Q').Homotopy (A'.symm.trans (L'.trans F')))
    (K : E.Homotopy (Q.trans G)) (K' : E'.Homotopy (Q'.trans G'))
    (hA : ∀ s, f (A s) = A' s) (hB : ∀ s, f (B s) = B' s)
    (hQ : ∀ s, f (Q s) = Q' s) (hL : ∀ s, f (L s) = L' s)
    (hF : ∀ s, f (F s) = F' s) (hE : ∀ s, f (E s) = E' s)
    (hG : ∀ s, f (G s) = G' s)
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (Path.Homotopy.pastedPositiveNullWord A B Q L F E G J K (r, s)) =
      Path.Homotopy.pastedPositiveNullWord A' B' Q' L' F' E' G' J' K' (r, s) := by
  have hAB := path_trans f A B A' B' hA hB
  exact comparison_trans f _ _ _ _
    (comparison_symm f _ _ (transAssoc f A B E A' B' E' hA hB hE))
    (comparison_trans f _ _ _ _
      (comparison_hcomp f _ _ _ _ (comparison_refl f (A.trans B) (A'.trans B') hAB) hK)
      (comparison_trans f _ _ _ _
        (comparison_symm f _ _
          (transAssoc f (A.trans B) Q G (A'.trans B') Q' G' hAB hQ hG))
        (comparison_trans f _ _ _ _
          (comparison_hcomp f _ _ _ _
            (straightPositiveWord f A B Q L F A' B' Q' L' F' J J'
              hA hB hQ hL hF hJ)
            (comparison_refl f G G' hG))
          (transAssoc f L F G L' F' G' hL hF hG)))) r s

end Path.Evaluation
