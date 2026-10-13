/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Prespectrum.FiberNaturality
public import Quillen.Topology.Prespectrum.FiberDetection

/-!
Original stable fiber coordinates, whole boundary naturality and the essential negative-degree
detection consumers.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.StableFiberFunctoriality

open Quillen
variable {A B C : Arrow LoopPrespectrum.{u}}

/-- Composition preserves both original source maps and the entire postcomposed path. -/
theorem composed_coordinates (sq : A ⟶ B) (sq' : B ⟶ C) (n : ℕ)
    (z : (homotopyFiber A.hom).space n) (s : unitInterval) :
    ((homotopyFiberMap (sq ≫ sq')).map n z).1.1 = sq'.left.map n (sq.left.map n z.1.1) ∧
    ((homotopyFiberMap (sq ≫ sq')).map n z).1.2 s = sq'.right.map n (sq.right.map n (z.1.2 s)) :=
  ⟨rfl,rfl⟩

/-- Identity preserves the original fiber object, not merely its homotopy class. -/
theorem identity_point (n : ℕ) (z : (homotopyFiber A.hom).space n) :
    (homotopyFiberMap (𝟙 A)).map n z = z := by apply Subtype.ext; rfl

/-- The degree-zero to negative-one boundary square is the original signed square. -/
theorem zero_negative_boundary (sq : A ⟶ B) :
    (stableHomotopyFunctor ((-1 : ℤ)+1)).map sq.right ≫ stableFiberConnecting B.hom (-1) =
      stableFiberConnecting A.hom (-1) ≫
        (stableHomotopyFunctor (-1)).map (homotopyFiberMap sq) :=
  stableFiberConnecting_naturality sq (-1)

/-- Naturality retains the full original nullhomotopy at every time. -/
theorem whole_nullhomotopy (sq : A ⟶ B) (n : ℕ)
    (z : (homotopyFiber A.hom).space n) (s : unitInterval) :
    (homotopyFiberNullHomotopy B.hom).level n (s,(homotopyFiberMap sq).map n z) =
      sq.right.map n ((homotopyFiberNullHomotopy A.hom).level n (s,z)) := rfl

/-- Stable side equivalences control the actual original map on fibers. -/
theorem original_fiber_equivalence (sq : A ⟶ B)
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map (homotopyFiberMap sq)) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (homotopyFiberMap_isStableEquivalence sq hl hr d)

/-- All original fiber classes vanish for a stable equivalence, including negative degrees. -/
theorem original_fiber_class_zero (h : IsStableEquivalence A.hom) (d : ℤ)
    (a : stableHomotopyGroup (homotopyFiber A.hom) d) : a = 0 :=
  (stableFiber_subsingleton_of_isStableEquivalence A.hom h d).elim _ _

/-- The actual negative-one fiber supplies degree-zero surjectivity, with no
positive-fiber condition silently substituted for it. -/
theorem zero_surjective_from_negative_fiber
    (h : Subsingleton (stableHomotopyGroup (homotopyFiber A.hom) (-1))) :
    Function.Surjective ((stableHomotopyFunctor ((-1 : ℤ)+1)).map A.hom) := by
  intro y
  exact (stableFiberConnecting_exact_target A.hom (-1) y).mp (h.elim _ _)

/-- The all-integer fiber criterion gives the original map, including degree zero. -/
theorem all_degrees_detect_original
    (h : ∀ d : ℤ, Subsingleton (stableHomotopyGroup (homotopyFiber A.hom) d)) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map A.hom) :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (isStableEquivalence_of_stableFiber_subsingleton A.hom h d)

end QuillenTest.StableFiberFunctoriality
