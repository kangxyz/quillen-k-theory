/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.ThreeRadialSquares
public import Quillen.Aglib.Topology.Path.EvaluationOperations

/-!
# Whole-value naturality of three radial squares

Intended upstream module: `Aglib.Topology.Path.ThreeRadialSquaresEvaluation`.

An arbitrary function preserving the ten constituent paths and three whole squares preserves
`ThreeRadialSquares.paste` at both original coordinates, with every original reassociation,
cast and cancellation clock. The actual consumer is the Laurent bottom face of the
three-triple polynomial cap comparison. No geometry or chosen filler is supplied by this lemma.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Path.Homotopy.ThreeRadialSquares
open Path.Evaluation
variable {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]

private theorem cancelLeft_eval (f : S → T) {o a b : S} {o' a' b' : T}
    (A : Path o a) (Y : Path a b) (A' : Path o' a') (Y' : Path a' b')
    (hA : ∀ s, f (A s) = A' s) (hY : ∀ s, f (Y s) = Y' s) (r s : I) :
    f (cancelLeft A Y (r, s)) = cancelLeft A' Y' (r, s) := by
  have hc : ∀ r s, f (reflSymmTrans A (r, s)) = reflSymmTrans A' (r, s) :=
    fun _ _ ↦ hA _
  exact comparison_trans f _ _ _ _
    (comparison_symm f _ _
      (Path.Evaluation.transAssoc f A.symm A Y A'.symm A' Y'
        (path_symm f A A' hA) hA hY))
    (comparison_trans f _ _ _ _
      (comparison_hcomp f _ _ _ _ (comparison_symm f _ _ hc) (fun _ s ↦ hY s))
      (fun _ _ ↦ hY _)) r s

private theorem cancelRight_eval (f : S → T) {o a b : S} {o' a' b' : T}
    (A : Path o a) (Y : Path o b) (A' : Path o' a') (Y' : Path o' b')
    (hA : ∀ s, f (A s) = A' s) (hY : ∀ s, f (Y s) = Y' s) (r s : I) :
    f (cancelRight A Y (r, s)) = cancelRight A' Y' (r, s) := by
  have hc : ∀ r s, f (reflTransSymm A (r, s)) = reflTransSymm A' (r, s) :=
    fun _ _ ↦ hA _
  exact comparison_trans f _ _ _ _
    (comparison_symm f _ _
      (Path.Evaluation.transAssoc f A A.symm Y A' A'.symm Y'
        hA (path_symm f A A' hA) hY))
    (comparison_trans f _ _ _ _
      (comparison_hcomp f _ _ _ _ (comparison_symm f _ _ hc) (fun _ s ↦ hY s))
      (fun _ _ ↦ hY _)) r s

private theorem removeRadial_eval (f : S → T) {o a b c : S} {o' a' b' c' : T}
    (A : Path o a) (X : Path a b) (Y : Path a c)
    (A' : Path o' a') (X' : Path a' b') (Y' : Path a' c')
    (hA : ∀ s, f (A s) = A' s) (hX : ∀ s, f (X s) = X' s)
    (hY : ∀ s, f (Y s) = Y' s) (r s : I) :
    f (removeRadial A X Y (r, s)) = removeRadial A' X' Y' (r, s) :=
  comparison_trans f _ _ _ _
    (Path.Evaluation.transAssoc f X.symm A.symm (A.trans Y) X'.symm A'.symm (A'.trans Y')
      (path_symm f X X' hX) (path_symm f A A' hA) (path_trans f A Y A' Y' hA hY))
    (comparison_hcomp f _ _ _ _ (fun _ s ↦ path_symm f X X' hX s)
      (cancelLeft_eval f A Y A' Y' hA hY)) r s

private theorem splice_eval (f : S → T) {o a b c : S} {o' a' b' c' : T}
    (P : Path o a) (Q : Path o b) (R : Path o c)
    (P' : Path o' a') (Q' : Path o' b') (R' : Path o' c')
    (hP : ∀ s, f (P s) = P' s) (hQ : ∀ s, f (Q s) = Q' s)
    (hR : ∀ s, f (R s) = R' s) (r s : I) :
    f (splice P Q R (r, s)) = splice P' Q' R' (r, s) :=
  comparison_trans f _ _ _ _
    (Path.Evaluation.transAssoc f P.symm Q (Q.symm.trans R) P'.symm Q' (Q'.symm.trans R')
      (path_symm f P P' hP) hQ (path_trans f Q.symm R Q'.symm R'
        (path_symm f Q Q' hQ) hR))
    (comparison_hcomp f _ _ _ _ (fun _ s ↦ path_symm f P P' hP s)
      (cancelRight_eval f Q R Q' R' hQ hR)) r s

/-- The original three-square paste preserves all pointwise path and square equations. -/
theorem paste_eval (f : S → T)
    {o a b c d z₀ z₁ z₂ : S} {o' a' b' c' d' z₀' z₁' z₂' : T}
    (A : Path o a) (B : Path o b) (C : Path o c) (D : Path o d)
    (X : Path a z₀) (Y : Path b z₀) (Z : Path b z₁) (W : Path c z₁)
    (V : Path c z₂) (U : Path d z₂)
    (A' : Path o' a') (B' : Path o' b') (C' : Path o' c') (D' : Path o' d')
    (X' : Path a' z₀') (Y' : Path b' z₀') (Z' : Path b' z₁') (W' : Path c' z₁')
    (V' : Path c' z₂') (U' : Path d' z₂')
    (J₁ : (A.trans X).Homotopy (B.trans Y))
    (J₂ : (C.trans W).Homotopy (B.trans Z))
    (J₃ : (C.trans V).Homotopy (D.trans U))
    (J₁' : (A'.trans X').Homotopy (B'.trans Y'))
    (J₂' : (C'.trans W').Homotopy (B'.trans Z'))
    (J₃' : (C'.trans V').Homotopy (D'.trans U'))
    (hA : ∀ s, f (A s) = A' s) (hB : ∀ s, f (B s) = B' s)
    (hC : ∀ s, f (C s) = C' s) (hD : ∀ s, f (D s) = D' s)
    (hX : ∀ s, f (X s) = X' s) (hY : ∀ s, f (Y s) = Y' s)
    (hZ : ∀ s, f (Z s) = Z' s) (hW : ∀ s, f (W s) = W' s)
    (hV : ∀ s, f (V s) = V' s) (hU : ∀ s, f (U s) = U' s)
    (hJ₁ : ∀ r s, f (J₁ (r, s)) = J₁' (r, s))
    (hJ₂ : ∀ r s, f (J₂ (r, s)) = J₂' (r, s))
    (hJ₃ : ∀ r s, f (J₃ (r, s)) = J₃' (r, s)) (r s : I) :
    f (paste A B C D X Y Z W V U J₁ J₂ J₃ (r, s)) =
      paste A' B' C' D' X' Y' Z' W' V' U' J₁' J₂' J₃' (r, s) := by
  have hAX := path_trans f A X A' X' hA hX
  have hCW := path_trans f C W C' W' hC hW
  have hDU := path_trans f D U D' U' hD hU
  have hJreverse : ∀ r s, f (J₁.symm.symm₂ (r, s)) = J₁'.symm.symm₂ (r, s) :=
    fun r s ↦ hJ₁ (unitInterval.symm r) (unitInterval.symm s)
  have hfirst := comparison_trans f _ _ _ _
    (comparison_symm f _ _ (removeRadial_eval f B Y Z B' Y' Z' hB hY hZ))
    (comparison_hcomp f _ _ _ _
      hJreverse
      (comparison_symm f _ _ hJ₂))
  have hsecond := comparison_trans f _ _ _ _
    (comparison_symm f _ _ (removeRadial_eval f C W V C' W' V' hC hW hV))
    (comparison_hcomp f (refl (C.trans W).symm) J₃
      (refl (C'.trans W').symm) J₃'
      (fun _ s ↦ path_symm f (C.trans W) (C'.trans W') hCW s) hJ₃)
  have hlast := comparison_trans f _ _ _ _
    (Path.Evaluation.transAssoc f X.symm A.symm (D.trans U) X'.symm A'.symm (D'.trans U')
      (path_symm f X X' hX) (path_symm f A A' hA) hDU)
    (comparison_hcomp f (refl X.symm) _ (refl X'.symm) _
      (fun _ s ↦ path_symm f X X' hX s)
      (comparison_symm f _ _
        (Path.Evaluation.transAssoc f A.symm D U A'.symm D' U'
          (path_symm f A A' hA) hD hU)))
  exact comparison_trans f _ _ _ _ (comparison_hcomp f _ _ _ _ hfirst hsecond)
    (comparison_trans f _ _ _ _
      (splice_eval f (A.trans X) (C.trans W) (D.trans U)
        (A'.trans X') (C'.trans W') (D'.trans U') hAX hCW hDU) hlast) r s

end Path.Homotopy.ThreeRadialSquares
