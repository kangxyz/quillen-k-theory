/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy

/-! # Actual moving-cylinder consumers of a proved boundary pasting -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.LoopPrespectrum.HomotopyPushout
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.HomotopySquareOfPasting
variable {A B C D : Quillen.LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {b₀ b₁ : B ⟶ D} {c₀ c₁ : C ⟶ D}
  {H₀ : Homotopy (f ≫ b₀) (g ≫ c₀)} {H₁ : Homotopy (f ≫ b₁) (g ≫ c₁)}
  (L : Homotopy b₀ b₁) (M : Homotopy c₀ c₁)
  (J : H₀.RelHomotopy
    (((Homotopy.precomp f L).trans H₁).trans (Homotopy.precomp g M).symm))

/-- The relative pasting alone supplies both actual moving boundary maps. -/
theorem original_moving_faces (n : ℕ) (r : unitInterval) (y : B.space n) (z : C.space n) :
    (descSquareHomotopy f g L M J.toSquare).level n (r, (inl f g).map n y) =
      L.level n (r, y) ∧
    (descSquareHomotopy f g L M J.toSquare).level n (r, (inr f g).map n z) =
      M.level n (r, z) :=
  ⟨descSquareHomotopy_inl f g L M J.toSquare n r y,
    descSquareHomotopy_inr f g L M J.toSquare n r z⟩

/-- Every original point of the relative comparison survives on the actual descended cylinder. -/
theorem original_comparison_cylinder (n : ℕ) (z : unitInterval × unitInterval)
    (x : A.space n) :
    (descSquareHomotopy f g L M J.toSquare).level n
      ((Quillen.ThreeSideSquare.collapse z).1,
        cylinder f g n ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      J.level n (z.1, (z.2, x)) :=
  J.toSquare_collapse n z x

/-- The structure coordinate is independent of both original comparison parameters. -/
theorem original_three_parameters (n : ℕ) (z : unitInterval × unitInterval)
    (t : unitInterval) (x : A.space n) :
    (descSquareHomotopy f g L M J.toSquare).level (n + 1)
      ((Quillen.ThreeSideSquare.collapse z).1,
        (prespectrum f g).structureMap n
          (cylinder f g n ((Quillen.ThreeSideSquare.collapse z).2, x)) t) =
      D.structureMap n (J.level n (z.1, (z.2, x))) t :=
  ((descSquareHomotopy f g L M J.toSquare).comm n
    (Quillen.ThreeSideSquare.collapse z).1
    (cylinder f g n ((Quillen.ThreeSideSquare.collapse z).2, x)) t).trans
      (congrArg (fun y ↦ D.structureMap n y t) (J.toSquare_collapse n z x))

/-- The output really joins the two original descended maps. -/
theorem original_descended_faces (n : ℕ) (q : Space f g n) :
    (descSquareHomotopy f g L M J.toSquare).level n (0, q) =
      (desc f g b₀ c₀ H₀).map n q ∧
    (descSquareHomotopy f g L M J.toSquare).level n (1, q) =
      (desc f g b₁ c₁ H₁).map n q :=
  ⟨(descSquareHomotopy f g L M J.toSquare).at_zero n q,
    (descSquareHomotopy f g L M J.toSquare).at_one n q⟩

/-- All four literal tracks have the prescribed orientation on the constructed rectangle. -/
theorem original_rectangle_faces (n : ℕ) (r s : unitInterval) (x : A.space n) :
    J.toSquare.level n (0, (s, x)) = H₀.level n (s, x) ∧
    J.toSquare.level n (1, (s, x)) = H₁.level n (s, x) ∧
    J.toSquare.level n (r, (0, x)) = L.level n (r, f.map n x) ∧
    J.toSquare.level n (r, (1, x)) = M.level n (r, g.map n x) :=
  ⟨J.toSquare.at_zero n s x, J.toSquare.at_one n s x,
    J.toSquare.left n r x, J.toSquare.right n r x⟩

end Quillen.Tests.HomotopySquareOfPasting
