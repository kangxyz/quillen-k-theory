/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.DoubleCylinderSquare

/-! # Exact old faces and full constant vertices of a supplied simplicial square -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.DoubleCylinderSquare
variable {X Y : SSet.{u}} (Q : (X ⊗ Δ[1]) ⊗ Δ[1] ⟶ Y)
  {f g : X ⟶ Y} (H : SSet.Homotopy f g)

/-- The two original cylinder inverses keep the original input, horizontal and vertical order. -/
theorem original_two_inverse_formula (t s : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (t, (s, x)) =
      SSet.toTop.map Q ((realizationCylinderIso (X ⊗ Δ[1])).inv
        ((realizationCylinderIso X).inv (x, ULift.up s), ULift.up t)) :=
  realizationDoubleCylinderSquare_apply Q t s x

/-- Outer time zero retains every point of the original inner homotopy. -/
theorem original_vertical_zero (h : SSet.ι₀ ≫ Q = H.h) (s : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (0, (s, x)) = realizationSimplicialHomotopy H (s, x) :=
  realizationDoubleCylinderSquare_vertical_zero Q H h s x

/-- Outer time one retains every point of the original inner homotopy. -/
theorem original_vertical_one (h : SSet.ι₁ ≫ Q = H.h) (s : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (1, (s, x)) = realizationSimplicialHomotopy H (s, x) :=
  realizationDoubleCylinderSquare_vertical_one Q H h s x

/-- Inner time zero retains every point of the original outer homotopy. -/
theorem original_horizontal_zero (h : (SSet.ι₀ ▷ Δ[1]) ≫ Q = H.h)
    (t : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (t, (0, x)) = realizationSimplicialHomotopy H (t, x) :=
  realizationDoubleCylinderSquare_horizontal_zero Q H h t x

/-- Inner time one retains every point of the original outer homotopy. -/
theorem original_horizontal_one (h : (SSet.ι₁ ▷ Δ[1]) ≫ Q = H.h)
    (t : unitInterval) (x : |X|) :
    realizationDoubleCylinderSquare Q (t, (1, x)) = realizationSimplicialHomotopy H (t, x) :=
  realizationDoubleCylinderSquare_horizontal_one Q H h t x

/-- The entire supplied vertex square keeps both original continuous times independent. -/
theorem whole_fixed_vertex (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (h : ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ▷ Δ[1]) ≫ Q =
      fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫ fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm y)
    (t s : unitInterval) :
    realizationDoubleCylinderSquare Q (t, (s, realizationPoint x)) = realizationPoint y :=
  realizationDoubleCylinderSquare_fixed_vertex Q x y h t s

end QuillenTest.DoubleCylinderSquare
