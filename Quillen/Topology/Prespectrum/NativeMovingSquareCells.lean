/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1EightEdges

/-! Exact native cells of moving-square pasting and the original identical-leg span square. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.Square
variable {E F : LoopPrespectrum.{u}} {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
  {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
  {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
  {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
  (S : H₀.Square H₁ L M) (T : K₀.Square K₁ M N)

/-- The original whole first half of a pasted square retains the exact first square. -/
theorem nativePastePaths_lower (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (S.pastePaths T).level n (r, (lower s, x)) = S.level n (r, (s, x)) := by
  change ContinuousMap.Homotopy.trans _ _ (lower s, (r, x)) = _
  exact Quillen.ScalarRectangle.homotopy_lower _ _ s (r, x)

/-- The whole other half includes the shared point and retains the second native square. -/
theorem nativePastePaths_upper (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (S.pastePaths T).level n (r, (upper s, x)) = T.level n (r, (s, x)) := by
  change ContinuousMap.Homotopy.trans _ _ (upper s, (r, x)) = _
  exact Quillen.ScalarRectangle.homotopy_upper _ _ s (r, x)
end Quillen.LoopPrespectrum.Homotopy.Square

namespace Quillen.LoopPrespectrum.HomotopyPushout
variable {A B A' B' : LoopPrespectrum.{u}} (f : A ⟶ B) (f' : A' ⟶ B')
  {a₀ a₁ : A ⟶ A'} {b₀ b₁ : B ⟶ B'}
  (H₀ : Homotopy (f ≫ b₀) (a₀ ≫ f')) (H₁ : Homotopy (f ≫ b₁) (a₁ ≫ f'))
  (L : Homotopy a₀ a₁) (M : Homotopy b₀ b₁)
  (S : H₀.Square H₁ (Homotopy.precomp f M) (L.postcomp f'))

/-- The first half is exactly the original polynomial square on the native left chart. -/
theorem identicalMoving_lower (n : ℕ) (r t : unitInterval) (x : A.space n) :
    (identicalLegMovingSquare f f' H₀ H₁ L M S).level n (r, (lower t, x)) =
      (inl f' f').map n (S.level n (r, (t, x))) := by
  unfold identicalLegMovingSquare
  rw [Homotopy.Square.nativePastePaths_lower]
  rfl

/-- The middle quarter retains both independent times in the original moving cylinder. -/
theorem identicalMoving_middle (n : ℕ) (r t : unitInterval) (x : A.space n) :
    (identicalLegMovingSquare f f' H₀ H₁ L M S).level n (r, (upper (lower t), x)) =
      cylinder f' f' n (t, L.level n (r, x)) := by
  unfold identicalLegMovingSquare
  rw [Homotopy.Square.nativePastePaths_upper, Homotopy.Square.nativePastePaths_lower]
  rfl

/-- The final quarter keeps the original reversed polynomial path on the distinct right chart. -/
theorem identicalMoving_upper (n : ℕ) (r t : unitInterval) (x : A.space n) :
    (identicalLegMovingSquare f f' H₀ H₁ L M S).level n (r, (upper (upper t), x)) =
      (inr f' f').map n (S.level n (r, (unitInterval.symm t, x))) := by
  unfold identicalLegMovingSquare
  rw [Homotopy.Square.nativePastePaths_upper, Homotopy.Square.nativePastePaths_upper]
  rfl

end Quillen.LoopPrespectrum.HomotopyPushout
