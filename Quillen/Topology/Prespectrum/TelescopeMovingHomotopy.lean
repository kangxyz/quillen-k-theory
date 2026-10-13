/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.Telescope
public import Quillen.Topology.Prespectrum.HomotopySquare

/-!
# Telescope descent of continuous squares with moving endpoints

Whole squares between the original cocone tracks, with the supplied stage
homotopies as their moving boundaries, descend to a genuine based prespectrum
homotopy of the original telescope desc maps. Currying in comparison time
precedes quotient descent. The full cylinder square and the independent
prespectrum structure coordinate are retained, without separation or local
compactness hypotheses on the stage spaces.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  {G : LoopPrespectrum.{u}} {a b : ∀ i, E i ⟶ G}
  {H : ∀ i, Homotopy (a i) (f i ≫ a (i + 1))}
  {K : ∀ i, Homotopy (b i) (f i ≫ b (i + 1))}
  (L : ∀ i, Homotopy (a i) (b i))
  (S : ∀ i, (H i).Square (K i) (L i) (Homotopy.precomp (f i) (L (i + 1))))

/-- The supplied whole square, curried in its independent comparison parameter. -/
def descSquarePiece (k i : ℕ) : C(unitInterval × (E i).space k, C(unitInterval, G.space k)) :=
  ContinuousMap.curry ⟨fun z ↦ (S i).level k (z.2, z.1), by fun_prop⟩

/-- The whole interval-valued map descends through the actual reduced telescope quotient. -/
def descSquareFamily (k : ℕ) : C(Space E f k, C(unitInterval, G.space k)) where
  toFun := Quot.lift (fun z ↦ descSquarePiece E f L S k z.1 z.2) (by
    intro x y h
    cases h with
    | step i x =>
      ext r
      exact ((S i).right k r x).trans ((S (i + 1)).left k r ((f i).map k x)).symm
    | base i s =>
      ext r
      exact ((S i).at_point k r s).trans ((S 0).at_point k r 0).symm)
  continuous_toFun := continuous_quot_lift _
    (continuous_sigma (fun i ↦ (descSquarePiece E f L S k i).continuous))

/-- Supplied moving-boundary squares induce a genuine homotopy of the original desc maps. -/
def descSquareHomotopy : Homotopy (desc E f a H) (desc E f b K) where
  level k := ⟨fun z ↦ descSquareFamily E f L S k z.2 z.1,
    (descSquareFamily E f L S k).uncurry.continuous.comp continuous_swap⟩
  at_zero k q := by
    induction q using Quot.inductionOn with
    | h z => exact (S z.1).at_zero k z.2.1 z.2.2
  at_one k q := by
    induction q using Quot.inductionOn with
    | h z => exact (S z.1).at_one k z.2.1 z.2.2
  at_point k r := (S 0).at_point k r 0
  comm k r q t := by
    induction q using Quot.inductionOn with
    | h z => exact (S z.1).comm k r z.2.1 z.2.2 t

/-- The whole original cylinder records the supplied square at both independent parameters. -/
@[simp] theorem descSquareHomotopy_cylinder (k i : ℕ) (r s : unitInterval)
    (x : (E i).space k) :
    (descSquareHomotopy E f L S).level k (r, cylinder E f k i (s, x)) =
      (S i).level k (r, (s, x)) := rfl

/-- Each original stage inclusion retains its entire supplied moving-endpoint track. -/
@[simp] theorem descSquareHomotopy_inclusion (k i : ℕ) (r : unitInterval)
    (x : (E i).space k) :
    (descSquareHomotopy E f L S).level k (r, (inclusion E f i).map k x) =
      (L i).level k (r, x) := (S i).left k r x

/-- Every comparison-time slice is the actual desc of the corresponding moving cocone. -/
theorem descSquareHomotopy_at (r : unitInterval) :
    (descSquareHomotopy E f L S).at r =
      desc E f (fun i ↦ (L i).at r) (fun i ↦ (S i).at r) := by
  apply hom_ext
  intro k i s x
  rfl

end Quillen.LoopPrespectrum.Telescope
