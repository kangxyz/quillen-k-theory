/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.SpanReassociationNaturality
public import Quillen.Topology.Path.NullWordEvaluation

/-!
# Shared pointwise operations in the original coherence consumers

The two imports share one implementation of the literal path operations. These clients
retain an arbitrary evaluator, an actual terminal pause or comparison reversal, and
independently selected comparison and path coordinates.
-/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace QuillenTest.PathEvaluationCoherence
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {a b c d e z : X} {a' b' c' d' e' z' : Y}

/-- A terminal pause preserves the actual three-stage word and both independently chosen times. -/
theorem reassociation_with_terminal_pause (f : X → Y)
    (P : Path a b) (Q : Path b c) (T : Path c d) (U : Path d e) (V : Path e z)
    (P' : Path a' b') (Q' : Path b' c') (T' : Path c' d')
    (U' : Path d' e') (V' : Path e' z')
    (hP : ∀ s, f (P s) = P' s) (hQ : ∀ s, f (Q s) = Q' s)
    (hT : ∀ s, f (T s) = T' s) (hU : ∀ s, f (U s) = U' s)
    (hV : ∀ s, f (V s) = V' s) (r s : I) :
    f (((Path.Homotopy.spanReassociation P Q T U V).trans
      (Path.Homotopy.refl ((P.trans Q).trans (T.trans (U.trans V))))) (r, s)) =
    ((Path.Homotopy.spanReassociation P' Q' T' U' V').trans
      (Path.Homotopy.refl ((P'.trans Q').trans (T'.trans (U'.trans V'))))) (r, s) := by
  apply Path.Evaluation.comparison_trans
  · exact Path.Evaluation.spanReassociation f P Q T U V P' Q' T' U' V'
      hP hQ hT hU hV
  · exact Path.Evaluation.comparison_refl f _ _
      (Path.Evaluation.path_trans f _ _ _ _
        (Path.Evaluation.path_trans f P Q P' Q' hP hQ)
        (Path.Evaluation.path_trans f T (U.trans V) T' (U'.trans V') hT
          (Path.Evaluation.path_trans f U V U' V' hU hV)))

/-- Reversing the complete straightening changes comparison time without reversing path time. -/
theorem reversed_straightening (f : X → Y)
    (A : Path a b) (B : Path b c) (Q : Path c d) (L : Path a e) (F : Path e d)
    (A' : Path a' b') (B' : Path b' c') (Q' : Path c' d')
    (L' : Path a' e') (F' : Path e' d')
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F)))
    (J' : (B'.trans Q').Homotopy (A'.symm.trans (L'.trans F')))
    (hA : ∀ s, f (A s) = A' s) (hB : ∀ s, f (B s) = B' s)
    (hQ : ∀ s, f (Q s) = Q' s) (hL : ∀ s, f (L s) = L' s)
    (hF : ∀ s, f (F s) = F' s)
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s)) (r s : I) :
    f ((Path.Homotopy.straightPositiveWord A B Q L F J).symm (r, s)) =
      (Path.Homotopy.straightPositiveWord A' B' Q' L' F' J').symm (r, s) :=
  Path.Evaluation.comparison_symm f _ _
    (Path.Evaluation.straightPositiveWord f A B Q L F A' B' Q' L' F' J J'
      hA hB hQ hL hF hJ) r s

end QuillenTest.PathEvaluationCoherence
