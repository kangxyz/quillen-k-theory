/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Prespectrum.FiberHomotopySquare

/-! Original square-track, whole loop-homotopy and negative-degree boundary consumers. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open Quillen Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.StableFiberHomotopySquare
variable {A B E F : LoopPrespectrum.{u}} (f : A ⟶ B) (g : E ⟶ F)
  (a : A ⟶ E) (b : B ⟶ F) (H : LoopPrespectrum.Homotopy (a ≫ g) (f ≫ b))

/-- Every supplied square-track value is retained in the actual fiber map. -/
theorem original_square_track (n : ℕ) (z : (homotopyFiber f).space n) (t : unitInterval) :
    ((homotopyFiberSquareMap f g a b H).map n z).1.2
      ⟨(t : ℝ)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩ = H.level n (t,z.1.1) :=
  homotopyFiberSquareMap_first_half f g a b H n z t

/-- The original source coordinate does not move during square-track insertion. -/
theorem original_source (n : ℕ) (z : (homotopyFiber f).space n) :
    ((homotopyFiberSquareMap f g a b H).map n z).1.1 = a.map n z.1.1 := rfl

/-- The connecting inclusion retains an actual homotopy of whole spectrum maps. -/
def wholeConnectingHomotopy :
    LoopPrespectrum.Homotopy
      (homotopyFiberLoopInclusion f ≫ homotopyFiberSquareMap f g a b H)
      (parameterLoopingMap b ≫ homotopyFiberLoopInclusion g) :=
  homotopyFiberSquareMapLoopHomotopy f g a b H

/-- A genuinely non-strict square still preserves the original 0-to-negative-one boundary. -/
theorem zero_negative_boundary :
    (stableHomotopyFunctor ((-1 : ℤ)+1)).map b ≫ stableFiberConnecting g (-1) =
      stableFiberConnecting f (-1) ≫
        (stableHomotopyFunctor (-1)).map (homotopyFiberSquareMap f g a b H) :=
  stableFiberConnecting_homotopySquare f g a b H (-1)

/-- The actual homotopy-square fiber map is used in every stable degree. -/
theorem original_stable_equivalence (ha : IsStableEquivalence a) (hb : IsStableEquivalence b)
    (d : ℤ) : Function.Bijective
      ((stableHomotopyFunctor d).map (homotopyFiberSquareMap f g a b H)) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (homotopyFiberSquareMap_isStableEquivalence f g a b H ha hb d)

end Quillen.Tests.StableFiberHomotopySquare
