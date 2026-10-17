/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.RetypedConeNullComparison

/-! Pointwise evaluation preserves the literal path operations without assuming continuity. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Path.Evaluation
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {a b c d e t : X} {a' b' c' d' e' t' : Y}

/-- Whole concatenation retains its original half cut under any pointwise evaluator. -/
theorem path_trans (f : X → Y) (p : Path a b) (q : Path b c)
    (p' : Path a' b') (q' : Path b' c')
    (hp : ∀ s, f (p s) = p' s) (hq : ∀ s, f (q s) = q' s) (s : I) :
    f ((p.trans q) s) = (p'.trans q') s := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

/-- Path reversal changes only the original path coordinate. -/
theorem path_symm (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (s : I) : f (p.symm s) = p'.symm s := hp _

/-- A constant comparison retains the complete supplied path. -/
theorem comparison_refl (f : X → Y) (p : Path a b) (p' : Path a' b')
    (hp : ∀ s, f (p s) = p' s) (r s : I) :
    f (Path.Homotopy.refl p (r, s)) = Path.Homotopy.refl p' (r, s) := hp s

/-- Comparison reversal does not reverse path time. -/
theorem comparison_symm (f : X → Y) {p q : Path a b} {p' q' : Path a' b'}
    (J : p.Homotopy q) (J' : p'.Homotopy q')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s)) (r s : I) :
    f (J.symm (r, s)) = J'.symm (r, s) := hJ _ s

/-- Vertical pasting changes comparison time at exactly the original half cut. -/
theorem comparison_trans (f : X → Y) {p q w : Path a b} {p' q' w' : Path a' b'}
    (J : p.Homotopy q) (K : q.Homotopy w)
    (J' : p'.Homotopy q') (K' : q'.Homotopy w')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (J.trans K (r, s)) = J'.trans K' (r, s) := by
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split_ifs
  · exact hJ _ s
  · exact hK _ s

/-- Horizontal pasting changes path time only, leaving comparison time independent. -/
theorem comparison_hcomp (f : X → Y)
    {p q : Path a b} {w z : Path b c} {p' q' : Path a' b'} {w' z' : Path b' c'}
    (J : p.Homotopy q) (K : w.Homotopy z)
    (J' : p'.Homotopy q') (K' : w'.Homotopy z')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (J.hcomp K (r, s)) = J'.hcomp K' (r, s) := by
  rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hJ r _
  · exact hK r _

/-- The literal associator uses the same reparameterized nested path on both sides. -/
theorem transAssoc (f : X → Y) (p : Path a b) (q : Path b c) (w : Path c d)
    (p' : Path a' b') (q' : Path b' c') (w' : Path c' d')
    (hp : ∀ s, f (p s) = p' s) (hq : ∀ s, f (q s) = q' s)
    (hw : ∀ s, f (w s) = w' s) (r s : I) :
    f (Path.Homotopy.transAssoc p q w (r, s)) =
      Path.Homotopy.transAssoc p' q' w' (r, s) :=
  path_trans f p (q.trans w) p' (q'.trans w') hp (path_trans f q w q' w' hq hw) _

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
