/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.CarrierSquareBoundary
public import Quillen.Topology.Path.NullWordEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyOperationEvaluation
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary
public import Quillen.Topology.Prespectrum.ConeSquareMapMovingCoherence

/-! Pointwise evaluation of the literal corrected boundary, retaining both pasting clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.CarrierPathSquare
open LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {a₀ b₀ a₁ b₁ : X}
  {p₀ : Path a₀ b₀} {p₁ p₂ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}
  {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
  {H₀ : Homotopy f₀ g₀} {H₁ H₂ : Homotopy f₁ g₁}
  {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}

/-- The exact native collapse and correction word, before quotient descent. -/
def nativeCorrectedBoundary (S : H₀.Square H₁ L M) (R : H₁.RelHomotopy H₂) :
    H₀.RelHomotopy ((L.trans H₂).trans M.symm) :=
  S.toBoundary.trans
    (((Homotopy.RelHomotopy.refl L).hcomp R).hcomp
      (Homotopy.RelHomotopy.refl M.symm))

/-- Whole square and correction images suffice; the evaluator need not be continuous. -/
theorem correctedBoundary_native (Q : Square p₀ p₁ l m) (J : p₁.Homotopy p₂)
    (S : H₀.Square H₁ L M) (R : H₁.RelHomotopy H₂)
    (n : ℕ) (x : E.space n) (ev : X → F.space n)
    (hQ : ∀ r s, ev (Q.parameter (r, s)) = S.level n (r, (s, x)))
    (hJ : ∀ r s, ev (J (r, s)) = R.level n (r, (s, x))) (r s : I) :
    ev ((Q.toBoundary.trans
      (((Path.Homotopy.refl l).hcomp J).hcomp (Path.Homotopy.refl m.symm))) (r, s)) =
      (nativeCorrectedBoundary S R).level n (r, (s, x)) := by
  have hL (t : I) : ev (l t) = L.level n (t, x) :=
    (congrArg ev (Q.left t)).symm.trans ((hQ t 0).trans (S.left n t x))
  have hM (t : I) : ev (m t) = M.level n (t, x) :=
    (congrArg ev (Q.right t)).symm.trans ((hQ t 1).trans (S.right n t x))
  have hB (r s : I) : ev (Q.toBoundary (r, s)) =
      S.toBoundary.level n (r, (s, x)) :=
    (hQ (ThreeSideSquare.collapse (r, s)).1
      (ThreeSideSquare.collapse (r, s)).2).trans
        (S.toBoundary_apply n r s x).symm
  have hC (r s : I) : ev (((Path.Homotopy.refl l).hcomp J) (r, s)) =
      ((Homotopy.RelHomotopy.refl L).hcomp R).level n (r, (s, x)) := by
    rw [Homotopy.RelHomotopy.hcomp_apply_path]
    exact Path.Evaluation.comparison_hcomp ev _ _ _ _ (fun _ t ↦ hL t) hJ r s
  have hD (r s : I) : ev
      ((((Path.Homotopy.refl l).hcomp J).hcomp (Path.Homotopy.refl m.symm)) (r, s)) =
      (((Homotopy.RelHomotopy.refl L).hcomp R).hcomp
        (Homotopy.RelHomotopy.refl M.symm)).level n (r, (s, x)) := by
    rw [Homotopy.RelHomotopy.hcomp_apply_path]
    exact Path.Evaluation.comparison_hcomp ev _ _ _ _ hC
      (fun _ t ↦ hM (unitInterval.symm t)) r s
  unfold nativeCorrectedBoundary
  rw [Homotopy.RelHomotopy.trans_apply_path]
  exact Path.Evaluation.comparison_trans ev _ _ _ _ hB hD r s

end Quillen.CarrierPathSquare

namespace Quillen.LoopPrespectrum
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))
  {e : E ⟶ E''} {l : F ⟶ F''} (T : Homotopy (f ≫ l) (e ≫ h))
  (A : Homotopy e (a ≫ c)) (B : Homotopy l (b ≫ d))
  (Q : T.Square (coneSquarePastedHomotopy f g h a b c d H K)
    (Homotopy.precomp f B) (A.postcomp h))

/-- The original corrected moving null square is precisely this full boundary descent. -/
theorem coneSquareCompositionMovingNullSquare_eq_boundary :
    coneSquareCompositionMovingNullSquare f g h a b c d H K T A B Q =
      (CarrierPathSquare.nativeCorrectedBoundary
        (coneSquareNullMovingSquare f h T
          (coneSquarePastedHomotopy f g h a b c d H K) A B Q)
        (coneSquareCompositionNullComparison f g h a b c d H K)).toSquare := rfl

end Quillen.LoopPrespectrum
