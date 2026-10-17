/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.ThreeRadialSquaresEvaluation

/-!
# Two evaluators for the literal three-radial-square paste

Intended upstream module: `Aglib.Topology.Path.ThreeRadialSquaresMapEvaluation`.
The target evaluator is continuous so its paths and squares can be mapped with only the
original concatenation endpoint casts. Two applications of `paste_eval` retain the original
unmapped target paste in the conclusion. The concrete consumer is the fixed eighteen-node
Laurent bottom face of the polynomial three-triple comparison.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v w
namespace Path.Homotopy.ThreeRadialSquares
variable {S : Type u} {T : Type v} {Z₀ : Type w}
  [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace Z₀]

/-- Compare two original pastes through an arbitrary source and continuous target evaluator. -/
theorem paste_eval_compare (f : S → Z₀) (g : C(T, Z₀))
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
    (hA : ∀ s, f (A s) = g (A' s)) (hB : ∀ s, f (B s) = g (B' s))
    (hC : ∀ s, f (C s) = g (C' s)) (hD : ∀ s, f (D s) = g (D' s))
    (hX : ∀ s, f (X s) = g (X' s)) (hY : ∀ s, f (Y s) = g (Y' s))
    (hZ : ∀ s, f (Z s) = g (Z' s)) (hW : ∀ s, f (W s) = g (W' s))
    (hV : ∀ s, f (V s) = g (V' s)) (hU : ∀ s, f (U s) = g (U' s))
    (hJ₁ : ∀ r s, f (J₁ (r, s)) = g (J₁' (r, s)))
    (hJ₂ : ∀ r s, f (J₂ (r, s)) = g (J₂' (r, s)))
    (hJ₃ : ∀ r s, f (J₃ (r, s)) = g (J₃' (r, s))) (r s : I) :
    f (paste A B C D X Y Z W V U J₁ J₂ J₃ (r, s)) =
      g (paste A' B' C' D' X' Y' Z' W' V' U' J₁' J₂' J₃' (r, s)) := by
  let M₁ : ((A'.map g.continuous).trans (X'.map g.continuous)).Homotopy
      ((B'.map g.continuous).trans (Y'.map g.continuous)) :=
    (J₁'.map g).cast (by simp only [Path.map_trans])
    (by simp only [Path.map_trans])
  let M₂ : ((C'.map g.continuous).trans (W'.map g.continuous)).Homotopy
      ((B'.map g.continuous).trans (Z'.map g.continuous)) :=
    (J₂'.map g).cast (by simp only [Path.map_trans])
    (by simp only [Path.map_trans])
  let M₃ : ((C'.map g.continuous).trans (V'.map g.continuous)).Homotopy
      ((D'.map g.continuous).trans (U'.map g.continuous)) :=
    (J₃'.map g).cast (by simp only [Path.map_trans])
    (by simp only [Path.map_trans])
  have hl := paste_eval f A B C D X Y Z W V U
    (A'.map g.continuous) (B'.map g.continuous) (C'.map g.continuous) (D'.map g.continuous)
    (X'.map g.continuous) (Y'.map g.continuous) (Z'.map g.continuous) (W'.map g.continuous)
    (V'.map g.continuous) (U'.map g.continuous)
    J₁ J₂ J₃ M₁ M₂ M₃ hA hB hC hD hX hY hZ hW hV hU hJ₁ hJ₂ hJ₃ r s
  have hr := paste_eval g A' B' C' D' X' Y' Z' W' V' U'
    (A'.map g.continuous) (B'.map g.continuous) (C'.map g.continuous) (D'.map g.continuous)
    (X'.map g.continuous) (Y'.map g.continuous) (Z'.map g.continuous) (W'.map g.continuous)
    (V'.map g.continuous) (U'.map g.continuous)
    J₁' J₂' J₃' M₁ M₂ M₃
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) r s
  exact hl.trans hr.symm

end Path.Homotopy.ThreeRadialSquares
