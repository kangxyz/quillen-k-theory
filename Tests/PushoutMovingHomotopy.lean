/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy

/-! Actual moving boundary maps and all independent cylinder/structure coordinates. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.LoopPrespectrum.HomotopyPushout
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.PushoutMovingHomotopy
variable {A B C D : Quillen.LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {b₀ b₁ : B ⟶ D} {c₀ c₁ : C ⟶ D}
  {H₀ : Homotopy (f ≫ b₀) (g ≫ c₀)} {H₁ : Homotopy (f ≫ b₁) (g ≫ c₁)}
  (L : Homotopy b₀ b₁) (M : Homotopy c₀ c₁)
  (S : H₀.Square H₁ (Homotopy.precomp f L) (Homotopy.precomp g M))

/-- Every original time slice restricts to the actual left moving map. -/
theorem original_left_slice (r : unitInterval) :
    inl f g ≫ (descSquareHomotopy f g L M S).at r = L.at r := by
  apply Hom.ext
  funext n
  ext y
  exact descSquareHomotopy_inl f g L M S n r y

/-- Every original time slice restricts to the actual right moving map. -/
theorem original_right_slice (r : unitInterval) :
    inr f g ≫ (descSquareHomotopy f g L M S).at r = M.at r := by
  apply Hom.ext
  funext n
  ext z
  exact descSquareHomotopy_inr f g L M S n r z

/-- The independent comparison, overlap and structure times retain the original structure map. -/
theorem original_three_parameters (n : ℕ) (r s t : unitInterval) (x : A.space n) :
    (descSquareHomotopy f g L M S).level (n + 1)
      (r, (prespectrum f g).structureMap n (cylinder f g n (s, x)) t) =
        D.structureMap n (S.level n (r, (s, x))) t :=
  (descSquareHomotopy f g L M S).comm n r (cylinder f g n (s, x)) t

/-- Both original descended maps are the literal first and last faces of the constructed
homotopy. -/
theorem original_descended_faces (n : ℕ) (q : Space f g n) :
    (descSquareHomotopy f g L M S).level n (0, q) = (desc f g b₀ c₀ H₀).map n q ∧
      (descSquareHomotopy f g L M S).level n (1, q) = (desc f g b₁ c₁ H₁).map n q :=
  ⟨(descSquareHomotopy f g L M S).at_zero n q,
    (descSquareHomotopy f g L M S).at_one n q⟩

/-- A genuine square obtained from any moving track, constant only in the overlap parameter. -/
def actualMovingSquare {E F : Quillen.LoopPrespectrum.{u}} {a b : E ⟶ F}
    (H : Homotopy a b) : (Homotopy.refl a).Square (Homotopy.refl b) H H where
  level n := ⟨fun z ↦ H.level n (z.1, z.2.2), by fun_prop⟩
  at_zero n _s x := H.at_zero n x
  at_one n _s x := H.at_one n x
  left _ _ _ := rfl
  right _ _ _ := rfl
  at_point n r _s := H.at_point n r
  comm n r _s x t := H.comm n r x t

/-- The identity span genuinely transports an arbitrary moving track on its whole cylinder. -/
theorem original_moving_identity_span {E F : Quillen.LoopPrespectrum.{u}} {a b : E ⟶ F}
    (H : Homotopy a b) (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (descSquareHomotopy (𝟙 E) (𝟙 E) H H (actualMovingSquare H)).level n
      (r, cylinder (𝟙 E) (𝟙 E) n (s, x)) = H.level n (r, x) := rfl

end Quillen.Tests.PushoutMovingHomotopy
