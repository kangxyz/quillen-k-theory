/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.NullWordEvaluation
public import Quillen.Aglib.Topology.Path.TwoSheetConjugation

/-!
# Pointwise naturality of the original two-sheet conjugation

The existing literal path operations preserve a function's supplied whole-path and whole-square
identities. This consumer retains the original conjugation recipe, independent endpoints and
both clocks. It depends on the existing null-word evaluation owner; no geometric compatibility
or choice of a cube is supplied here. The actual consumer is composite J0 carrier transport.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Path.Evaluation
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem symmPath_eval (ev : X → Y) {a b : X} {a' b' : Y}
    {p q : Path a b} {p' q' : Path a' b'}
    (J : p.Homotopy q) (J' : p'.Homotopy q')
    (h : ∀ r s, ev (J (r, s)) = J' (r, s)) (r s : I) :
    ev (J.symm₂ (r, s)) = J'.symm₂ (r, s) := h r _

private theorem reflSymmTrans_eval (ev : X → Y) {a b : X} {a' b' : Y}
    (p : Path a b) (p' : Path a' b')
    (h : ∀ s, ev (p s) = p' s) (r s : I) :
    ev (Path.Homotopy.reflSymmTrans p (r, s)) =
      Path.Homotopy.reflSymmTrans p' (r, s) :=
  reflTransSymm ev p.symm p'.symm (path_symm ev p p' h) r s

private theorem retypeSource_eval (ev : X → Y)
    {a b c d : X} {a' b' c' d' : Y}
    (L : Path a b) (N : Path b c) (W : Path a d) (Z : Path c d)
    (L' : Path a' b') (N' : Path b' c') (W' : Path a' d') (Z' : Path c' d')
    (J : ((N.symm.trans L.symm).trans W).Homotopy Z)
    (J' : ((N'.symm.trans L'.symm).trans W').Homotopy Z')
    (h : ∀ r s, ev (J (r, s)) = J' (r, s)) (r s : I) :
    ev (Path.Homotopy.TwoSheetConjugation.retypeSource L N W Z J (r, s)) =
      Path.Homotopy.TwoSheetConjugation.retypeSource L' N' W' Z' J' (r, s) := h r s

/-- Whole constituent equations preserve the exact two-sheet conjugation at both original times. -/
theorem twoSheetConjugation (ev : X → Y)
    {a₀ a₁ b₀ b₁ c₀ c₁ : X} {a₀' a₁' b₀' b₁' c₀' c₁' : Y}
    (U : Path a₀ a₁) (V : Path b₀ b₁) (L₀ : Path a₀ b₀) (L₁ : Path a₁ b₁)
    (N₀₀ : Path a₀ c₀) (N₀₁ : Path a₁ c₁) (N₁₀ : Path b₀ c₀) (N₁₁ : Path b₁ c₁)
    (U' : Path a₀' a₁') (V' : Path b₀' b₁')
    (L₀' : Path a₀' b₀') (L₁' : Path a₁' b₁')
    (N₀₀' : Path a₀' c₀') (N₀₁' : Path a₁' c₁')
    (N₁₀' : Path b₀' c₀') (N₁₁' : Path b₁' c₁')
    (JU : (U.trans L₁).Homotopy (L₀.trans V))
    (JN₀ : N₀₀.Homotopy (L₀.trans N₁₀)) (JN₁ : N₀₁.Homotopy (L₁.trans N₁₁))
    (JU' : (U'.trans L₁').Homotopy (L₀'.trans V'))
    (JN₀' : N₀₀'.Homotopy (L₀'.trans N₁₀'))
    (JN₁' : N₀₁'.Homotopy (L₁'.trans N₁₁'))
    (hU : ∀ s, ev (U s) = U' s) (hV : ∀ s, ev (V s) = V' s)
    (hL₀ : ∀ s, ev (L₀ s) = L₀' s) (hL₁ : ∀ s, ev (L₁ s) = L₁' s)
    (hN₁₀ : ∀ s, ev (N₁₀ s) = N₁₀' s) (hN₁₁ : ∀ s, ev (N₁₁ s) = N₁₁' s)
    (hJU : ∀ r s, ev (JU (r, s)) = JU' (r, s))
    (hJN₀ : ∀ r s, ev (JN₀ (r, s)) = JN₀' (r, s))
    (hJN₁ : ∀ r s, ev (JN₁ (r, s)) = JN₁' (r, s)) (r s : I) :
    ev (Path.Homotopy.TwoSheetConjugation.comparison
      U V L₀ L₁ N₀₀ N₀₁ N₁₀ N₁₁ JU JN₀ JN₁ (r, s)) =
      Path.Homotopy.TwoSheetConjugation.comparison
        U' V' L₀' L₁' N₀₀' N₀₁' N₁₀' N₁₁' JU' JN₀' JN₁' (r, s) := by
  have hW := path_trans ev V N₁₁ V' N₁₁' hV hN₁₁
  have hLN := path_trans ev L₁ N₁₁ L₁' N₁₁' hL₁ hN₁₁
  have hULN := path_trans ev U (L₁.trans N₁₁) U' (L₁'.trans N₁₁') hU hLN
  have hJUstep := comparison_trans ev _ _ _ _
    (comparison_symm ev _ _ (transAssoc ev U L₁ N₁₁ U' L₁' N₁₁' hU hL₁ hN₁₁))
    (comparison_trans ev _ _ _ _
      (comparison_hcomp ev _ _ _ _ hJU (comparison_refl ev N₁₁ N₁₁' hN₁₁))
      (transAssoc ev L₀ V N₁₁ L₀' V' N₁₁' hL₀ hV hN₁₁))
  have hJC := comparison_trans ev _ _ _ _
    (comparison_symm ev _ _
      (transAssoc ev L₀.symm L₀ (V.trans N₁₁) L₀'.symm L₀' (V'.trans N₁₁')
        (path_symm ev L₀ L₀' hL₀) hL₀ hW))
    (comparison_trans ev _ _ _ _
      (comparison_hcomp ev _ _ _ _
        (comparison_symm ev _ _ (reflSymmTrans_eval ev L₀ L₀' hL₀))
        (comparison_refl ev (V.trans N₁₁) (V'.trans N₁₁') hW))
      (reflTrans ev (V.trans N₁₁) (V'.trans N₁₁') hW))
  have hJ := retypeSource_eval ev L₀ N₁₀ (U.trans (L₁.trans N₁₁))
    (N₁₀.symm.trans (V.trans N₁₁)) L₀' N₁₀' (U'.trans (L₁'.trans N₁₁'))
    (N₁₀'.symm.trans (V'.trans N₁₁')) _ _
    (comparison_trans ev _ _ _ _
      (transAssoc ev N₁₀.symm L₀.symm (U.trans (L₁.trans N₁₁))
        N₁₀'.symm L₀'.symm (U'.trans (L₁'.trans N₁₁'))
        (path_symm ev N₁₀ N₁₀' hN₁₀) (path_symm ev L₀ L₀' hL₀) hULN)
      (comparison_hcomp ev _ _ _ _
        (comparison_refl ev N₁₀.symm N₁₀'.symm (path_symm ev N₁₀ N₁₀' hN₁₀))
        (comparison_trans ev _ _ _ _
          (comparison_hcomp ev _ _ _ _
            (comparison_refl ev L₀.symm L₀'.symm (path_symm ev L₀ L₀' hL₀))
            hJUstep) hJC)))
  exact comparison_trans ev _ _ _ _
    (comparison_hcomp ev _ _ _ _ (symmPath_eval ev _ _ hJN₀)
      (comparison_hcomp ev _ _ _ _ (comparison_refl ev U U' hU) hJN₁)) hJ r s

end Path.Evaluation
