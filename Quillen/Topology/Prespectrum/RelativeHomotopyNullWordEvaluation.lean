/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.NullWordEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyOperationEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyAssociatorEvaluation

/-! Pointwise native evaluation of the two literal five-stage null-comparison words. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.NativeNullWordEvaluation
open LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {a b c d e t : X}
  {E T : LoopPrespectrum.{u}} {f0 f1 f2 f3 f4 f5 : E ⟶ T}
  (n : ℕ) (x : E.space n) (ev : X → T.space n)
namespace Word
open Homotopy.RelHomotopy
/-- The literal five-stage original straight-positive comparison word. -/
def straightPositiveWord (A : Homotopy f0 f1) (B : Homotopy f1 f2) (Q : Homotopy f2 f3)
    (L : Homotopy f0 f4) (F : Homotopy f4 f3)
    (J : (B.trans Q).RelHomotopy (A.symm.trans (L.trans F))) :
    ((A.trans B).trans Q).RelHomotopy (L.trans F) :=
  (transAssoc A B Q).trans
    (((refl A).hcomp J).trans
      ((transAssoc A A.symm (L.trans F)).symm.trans
        (((reflTransSymm A).symm.hcomp (refl (L.trans F))).trans
          (reflTrans (L.trans F)))))

/-- The literal five-stage null comparison; neither clock nor terminal pause is flattened. -/
def pastedPositiveNullWord (A : Homotopy f0 f1) (B : Homotopy f1 f2) (Q : Homotopy f2 f3)
    (L : Homotopy f0 f4) (F : Homotopy f4 f3) (E : Homotopy f2 f5) (G : Homotopy f3 f5)
    (J : (B.trans Q).RelHomotopy (A.symm.trans (L.trans F)))
    (K : E.RelHomotopy (Q.trans G)) :
    (A.trans (B.trans E)).RelHomotopy (L.trans (F.trans G)) :=
  (transAssoc A B E).symm.trans
    (((refl (A.trans B)).hcomp K).trans
      ((transAssoc (A.trans B) Q G).symm.trans
        (((straightPositiveWord A B Q L F J).hcomp (refl G)).trans
          (transAssoc L F G))))

end Word

private theorem path_trans (p : Path a b) (q : Path b c)
    (H : Homotopy f0 f1) (K : Homotopy f1 f2)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x)) (s : I) :
    ev ((p.trans q) s) = (H.trans K).level n (s, x) := by
  change ev ((p.trans q) s) = (H.trans K).path n x s
  rw [Homotopy.path_trans]
  exact Path.Evaluation.path_trans ev p q (H.path n x) (K.path n x) hp hq s

private theorem path_symm (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (s : I) :
    ev (p.symm s) = H.symm.level n (s, x) := hp _

private theorem comparison_refl (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.refl p (r, s)) =
      (Homotopy.RelHomotopy.refl H).level n (r, (s, x)) := hp s

private theorem comparison_symm {p q : Path a b} {H K : Homotopy f0 f1}
    (J : p.Homotopy q) (J' : H.RelHomotopy K)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x))) (r s : I) :
    ev (J.symm (r, s)) = J'.symm.level n (r, (s, x)) := hJ _ s

private theorem comparison_trans {p q w : Path a b} {H K L : Homotopy f0 f1}
    (J : p.Homotopy q) (K' : q.Homotopy w)
    (J' : H.RelHomotopy K) (L' : K.RelHomotopy L)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hK : ∀ r s, ev (K' (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.trans K' (r, s)) = (J'.trans L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.trans_apply_path]
  exact Path.Evaluation.comparison_trans ev J K' (J'.path n x) (L'.path n x) hJ hK r s

private theorem comparison_hcomp {p q : Path a b} {w z : Path b c}
    {H H' : Homotopy f0 f1} {K K' : Homotopy f1 f2}
    (J : p.Homotopy q) (L : w.Homotopy z)
    (J' : H.RelHomotopy H') (L' : K.RelHomotopy K')
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hL : ∀ r s, ev (L (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.hcomp L (r, s)) = (J'.hcomp L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.hcomp_apply_path]
  exact Path.Evaluation.comparison_hcomp ev J L (J'.path n x) (L'.path n x) hJ hL r s

private theorem transAssoc (p : Path a b) (q : Path b c) (w : Path c d)
    (H : Homotopy f0 f1) (K : Homotopy f1 f2) (L : Homotopy f2 f3)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x))
    (hw : ∀ s, ev (w s) = L.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.transAssoc p q w (r, s)) =
      (Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.transAssoc_apply_path]
  exact Path.Evaluation.transAssoc ev p q w (H.path n x) (K.path n x) (L.path n x)
    hp hq hw r s

private theorem reflTransSymm (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.reflTransSymm p (r, s)) =
      (Homotopy.RelHomotopy.reflTransSymm H).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.reflTransSymm_apply_path]
  exact Path.Evaluation.reflTransSymm ev p (H.path n x) hp r s

private theorem reflTrans (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.reflTrans p (r, s)) =
      (Homotopy.RelHomotopy.reflTrans H).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.reflTrans_apply_path]
  exact Path.Evaluation.reflTrans ev p (H.path n x) hp r s

/-- The five-stage straightening word keeps every original comparison and path cut. -/
theorem straightPositiveWord
    (A : Path a b) (B : Path b c) (Q : Path c d) (L : Path a e) (F : Path e d)
    (A' : Homotopy f0 f1) (B' : Homotopy f1 f2) (Q' : Homotopy f2 f3)
    (L' : Homotopy f0 f4) (F' : Homotopy f4 f3)
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F)))
    (J' : (B'.trans Q').RelHomotopy (A'.symm.trans (L'.trans F')))
    (hA : ∀ s, ev (A s) = A'.level n (s, x)) (hB : ∀ s, ev (B s) = B'.level n (s, x))
    (hQ : ∀ s, ev (Q s) = Q'.level n (s, x)) (hL : ∀ s, ev (L s) = L'.level n (s, x))
    (hF : ∀ s, ev (F s) = F'.level n (s, x))
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x))) (r s : I) :
    ev (Path.Homotopy.straightPositiveWord A B Q L F J (r, s)) =
      (Word.straightPositiveWord A' B' Q' L' F' J').level n (r, (s, x)) := by
  have hT := path_trans n x ev L F L' F' hL hF
  exact comparison_trans n x ev _ _ _ _ (transAssoc n x ev A B Q A' B' Q' hA hB hQ)
    (comparison_trans n x ev _ _ _ _
      (comparison_hcomp n x ev _ _ _ _ (comparison_refl n x ev A A' hA) hJ)
      (comparison_trans n x ev _ _ _ _
        (comparison_symm n x ev _ _
          (transAssoc n x ev A A.symm (L.trans F) A' A'.symm (L'.trans F')
            hA (path_symm n x ev A A' hA) hT))
        (comparison_trans n x ev _ _ _ _
          (comparison_hcomp n x ev _ _ _ _
            (comparison_symm n x ev _ _ (reflTransSymm n x ev A A' hA))
            (comparison_refl n x ev (L.trans F) (L'.trans F') hT))
          (reflTrans n x ev (L.trans F) (L'.trans F') hT)))) r s

/-- The complete pasted-null word preserves its five nested comparison stages. -/
theorem pastedPositiveNullWord
    (A : Path a b) (B : Path b c) (Q : Path c d) (L : Path a e) (F : Path e d)
    (E : Path c t) (G : Path d t)
    (A' : Homotopy f0 f1) (B' : Homotopy f1 f2) (Q' : Homotopy f2 f3)
    (L' : Homotopy f0 f4) (F' : Homotopy f4 f3) (E' : Homotopy f2 f5) (G' : Homotopy f3 f5)
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F)))
    (J' : (B'.trans Q').RelHomotopy (A'.symm.trans (L'.trans F')))
    (K : E.Homotopy (Q.trans G)) (K' : E'.RelHomotopy (Q'.trans G'))
    (hA : ∀ s, ev (A s) = A'.level n (s, x)) (hB : ∀ s, ev (B s) = B'.level n (s, x))
    (hQ : ∀ s, ev (Q s) = Q'.level n (s, x)) (hL : ∀ s, ev (L s) = L'.level n (s, x))
    (hF : ∀ s, ev (F s) = F'.level n (s, x)) (hE : ∀ s, ev (E s) = E'.level n (s, x))
    (hG : ∀ s, ev (G s) = G'.level n (s, x))
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hK : ∀ r s, ev (K (r, s)) = K'.level n (r, (s, x))) (r s : I) :
    ev (Path.Homotopy.pastedPositiveNullWord A B Q L F E G J K (r, s)) =
      (Word.pastedPositiveNullWord A' B' Q' L' F' E' G' J' K').level n (r, (s, x)) := by
  have hAB := path_trans n x ev A B A' B' hA hB
  exact comparison_trans n x ev _ _ _ _
    (comparison_symm n x ev _ _ (transAssoc n x ev A B E A' B' E' hA hB hE))
    (comparison_trans n x ev _ _ _ _
      (comparison_hcomp n x ev _ _ _ _ (comparison_refl n x ev (A.trans B) (A'.trans B') hAB) hK)
      (comparison_trans n x ev _ _ _ _
        (comparison_symm n x ev _ _
          (transAssoc n x ev (A.trans B) Q G (A'.trans B') Q' G' hAB hQ hG))
        (comparison_trans n x ev _ _ _ _
          (comparison_hcomp n x ev _ _ _ _
            (straightPositiveWord n x ev A B Q L F A' B' Q' L' F' J J'
              hA hB hQ hL hF hJ)
            (comparison_refl n x ev G G' hG))
          (transAssoc n x ev L F G L' F' G' hL hF hG)))) r s

end Quillen.NativeNullWordEvaluation
