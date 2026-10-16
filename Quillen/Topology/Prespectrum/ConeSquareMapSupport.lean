/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.ConeSquareMapMovingCoherence

/-!
# Pointwise support of the original moving cone composition

Equality of two comparison squares on one source point is preserved through the actual
moving-null construction: path pasting, boundary collapse, the unchanged relative null
comparison, and the square lift. No square or higher filler is constructed or assumed here
beyond the two comparison squares explicitly being compared.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
namespace Homotopy.Square

/-- Path pasting preserves pointwise equality at the same source point and independent times. -/
theorem pastePaths_apply_congr {E F : LoopPrespectrum.{u}}
    {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (S S' : H₀.Square H₁ L M) (T T' : K₀.Square K₁ M N)
    (n : ℕ) (x : E.space n)
    (hS : ∀ r s, S.level n (r, (s, x)) = S'.level n (r, (s, x)))
    (hT : ∀ r s, T.level n (r, (s, x)) = T'.level n (r, (s, x)))
    (r s : unitInterval) :
    (S.pastePaths T).level n (r, (s, x)) =
      (S'.pastePaths T').level n (r, (s, x)) := by
  unfold pastePaths
  dsimp only [ContinuousMap.coe_mk]
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact hS r _
  · exact hT r _

/-- The fixed boundary collapse does not change the source point at which squares agree. -/
theorem toBoundary_apply_congr {E F : LoopPrespectrum.{u}} {a₀ b₀ a₁ b₁ : E ⟶ F}
    {H₀ : Homotopy a₀ b₀} {H₁ : Homotopy a₁ b₁}
    {L : Homotopy a₀ a₁} {M : Homotopy b₀ b₁}
    (S S' : H₀.Square H₁ L M) (n : ℕ) (x : E.space n)
    (hS : ∀ r s, S.level n (r, (s, x)) = S'.level n (r, (s, x)))
    (r s : unitInterval) :
    S.toBoundary.level n (r, (s, x)) = S'.toBoundary.level n (r, (s, x)) :=
  hS (Quillen.ThreeSideSquare.collapse (r, s)).1
    (Quillen.ThreeSideSquare.collapse (r, s)).2

end Homotopy.Square
namespace Homotopy.RelHomotopy

/-- Relative concatenation preserves the same pointwise support in both of its actual pieces. -/
theorem trans_apply_congr {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K L : Homotopy f g} (J J' : H.RelHomotopy K) (N N' : K.RelHomotopy L)
    (n : ℕ) (x : E.space n)
    (hJ : ∀ r s, J.level n (r, (s, x)) = J'.level n (r, (s, x)))
    (hN : ∀ r s, N.level n (r, (s, x)) = N'.level n (r, (s, x)))
    (r s : unitInterval) :
    (J.trans N).level n (r, (s, x)) = (J'.trans N').level n (r, (s, x)) := by
  change ((J.level n).trans (N.level n)) (r, (s, x)) =
    ((J'.level n).trans (N'.level n)) (r, (s, x))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hN _ s

/-- The actual square lift preserves equality on a source point, using surjectivity of its
fixed collapse and the original collapse formula rather than choosing a new filler. -/
theorem toSquare_apply_congr {E F : LoopPrespectrum.{u}} {a₀ b₀ a₁ b₁ : E ⟶ F}
    {H₀ : Homotopy a₀ b₀} {H₁ : Homotopy a₁ b₁}
    {L : Homotopy a₀ a₁} {M : Homotopy b₀ b₁}
    (J J' : H₀.RelHomotopy ((L.trans H₁).trans M.symm))
    (n : ℕ) (x : E.space n)
    (hJ : ∀ r s, J.level n (r, (s, x)) = J'.level n (r, (s, x)))
    (r s : unitInterval) :
    J.toSquare.level n (r, (s, x)) = J'.toSquare.level n (r, (s, x)) := by
  obtain ⟨z, hz⟩ := Quillen.ThreeSideSquare.collapse_surjective (r, s)
  have hr := congrArg Prod.fst hz
  have hs := congrArg Prod.snd hz
  change (Quillen.ThreeSideSquare.collapse z).1 = r at hr
  change (Quillen.ThreeSideSquare.collapse z).2 = s at hs
  rw [← hr, ← hs, toSquare_collapse, toSquare_collapse]
  exact hJ z.1 z.2

end Homotopy.RelHomotopy

section Moving
variable {E F E' F' : LoopPrespectrum.{u}} (f : E ⟶ F) (g : E' ⟶ F')
  {a₀ a₁ : E ⟶ E'} {b₀ b₁ : F ⟶ F'}
  (H : Homotopy (f ≫ b₀) (a₀ ≫ g)) (K : Homotopy (f ≫ b₁) (a₁ ≫ g))
  (A : Homotopy a₀ a₁) (B : Homotopy b₀ b₁)
  (Q Q' : H.Square K (Homotopy.precomp f B) (A.postcomp g))

/-- The comparison-square contribution to the moving null retains exactly its original support;
the independent cone interchange is the same on both sides. -/
theorem coneSquareNullMovingSquare_apply_congr (n : ℕ) (x : E.space n)
    (hQ : ∀ r s, Q.level n (r, (s, x)) = Q'.level n (r, (s, x)))
    (r s : unitInterval) :
    (coneSquareNullMovingSquare f g H K A B Q).level n (r, (s, x)) =
      (coneSquareNullMovingSquare f g H K A B Q').level n (r, (s, x)) := by
  unfold coneSquareNullMovingSquare
  apply Homotopy.Square.pastePaths_apply_congr
  · intro r' s'
    exact congrArg ((mappingConeInclusion g).map n) (hQ r' s')
  · intro _ _
    rfl

end Moving
section Composition
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))
  {e : E ⟶ E''} {l : F ⟶ F''} (T : Homotopy (f ≫ l) (e ≫ h))
  (A : Homotopy e (a ≫ c)) (B : Homotopy l (b ≫ d))
  (Q Q' : T.Square (coneSquarePastedHomotopy f g h a b c d H K)
    (Homotopy.precomp f B) (A.postcomp h))

/-- Pointwise support survives the entire original moving-null composition construction:
toBoundary, relative trans with both unchanged hcomp/null-comparison factors, and toSquare. -/
theorem coneSquareCompositionMovingNullSquare_apply_congr (n : ℕ) (x : E.space n)
    (hQ : ∀ r s, Q.level n (r, (s, x)) = Q'.level n (r, (s, x)))
    (r s : unitInterval) :
    (coneSquareCompositionMovingNullSquare f g h a b c d H K T A B Q).level n
      (r, (s, x)) =
    (coneSquareCompositionMovingNullSquare f g h a b c d H K T A B Q').level n
      (r, (s, x)) := by
  unfold coneSquareCompositionMovingNullSquare
  apply Homotopy.RelHomotopy.toSquare_apply_congr
  intro r' s'
  apply Homotopy.RelHomotopy.trans_apply_congr
  · intro r'' s''
    apply Homotopy.Square.toBoundary_apply_congr
    intro r''' s'''
    exact coneSquareNullMovingSquare_apply_congr f h T
      (coneSquarePastedHomotopy f g h a b c d H K) A B Q Q' n x hQ r''' s'''
  · intro _ _
    rfl

end Composition
end Quillen.LoopPrespectrum
