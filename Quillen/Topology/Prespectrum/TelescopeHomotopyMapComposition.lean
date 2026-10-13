/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeRelativeHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Actual composition homotopies for track-defined telescope maps

The canonical composite transition track first traverses the second diagram's
transition homotopy and then the first one's. Reassociation of the three actual
cylinder tracks gives a relative comparison and hence a genuine prespectrum
homotopy from the original composite telescope map to its track-defined map.
No separation or compactness hypotheses are needed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
  (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
  (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
  (H : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1)))
  (K : ∀ i, Homotopy (b i ≫ h i) (g i ≫ b (i + 1)))

/-- The canonical whole transition track for the composite stage maps. -/
def composeTransitionHomotopy (i : ℕ) :
    Homotopy ((a i ≫ b i) ≫ h i) (f i ≫ (a (i + 1) ≫ b (i + 1))) :=
  ((Homotopy.precomp (a i) (K i)).trans
    (((H i).postcomp (b (i + 1))).cast (Category.assoc _ _ _) (Category.assoc _ _ _))).cast
      (Category.assoc _ _ _).symm rfl

/-- The literal composite-map cylinder track, with only endpoint-arrow transport. -/
def compositeMapCoconeHomotopy (i : ℕ) :
    Homotopy ((a i ≫ b i) ≫ inclusion G h i)
      (f i ≫ ((a (i + 1) ≫ b (i + 1)) ≫ inclusion G h (i + 1))) :=
  ((mapCoconeHomotopy E f F g a H i).postcomp (mapOfHomotopies F g G h b K)).cast
    (by rw [Category.assoc, inclusion_mapOfHomotopies, ← Category.assoc])
    (by simp only [Category.assoc, inclusion_mapOfHomotopies])

/-- Reassociate the three original tracks without changing their endpoints or basepoint line. -/
def mapCoconeCompositionRelHomotopy (i : ℕ) :
    (compositeMapCoconeHomotopy E f F g G h a b H K i).RelHomotopy
      (mapCoconeHomotopy E f G h (fun j ↦ a j ≫ b j)
        (composeTransitionHomotopy E f F g G h a b H K) i) := by
  let A := Homotopy.precomp (a i ≫ b i) (inclusionHomotopy G h i)
  let B := ((Homotopy.precomp (a i) (K i)).postcomp (inclusion G h (i + 1))).cast
    (show (a i ≫ (b i ≫ h i)) ≫ inclusion G h (i + 1) =
      (a i ≫ b i) ≫ (h i ≫ inclusion G h (i + 1)) by simp only [Category.assoc]) rfl
  let C := ((H i).postcomp (b (i + 1) ≫ inclusion G h (i + 1))).cast
    (show (a i ≫ g i) ≫ (b (i + 1) ≫ inclusion G h (i + 1)) =
      (a i ≫ (g i ≫ b (i + 1))) ≫ inclusion G h (i + 1) by simp only [Category.assoc])
    (show (f i ≫ a (i + 1)) ≫ (b (i + 1) ≫ inclusion G h (i + 1)) =
      f i ≫ ((a (i + 1) ≫ b (i + 1)) ≫ inclusion G h (i + 1)) by simp only [Category.assoc])
  apply (Homotopy.RelHomotopy.transAssoc A B C).ofLevels
  · intro n
    change ((mapCoconeHomotopy E f F g a H i).postcomp
      (mapOfHomotopies F g G h b K)).level n = ((A.trans B).trans C).level n
    unfold mapCoconeHomotopy
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · calc
        _ = (Homotopy.precomp (a i) (mapCoconeHomotopy F g G h b K i)).level n := by
          apply ContinuousMap.ext
          intro z
          rfl
        _ = _ := by
          unfold mapCoconeHomotopy
          rw [Homotopy.precomp_trans]
          apply Homotopy.trans_level_congr <;> rfl
    · apply ContinuousMap.ext
      intro z
      exact congrArg (fun q ↦ q.map n ((H i).level n z))
        (inclusion_mapOfHomotopies F g G h b K (i + 1))
  · intro n
    change (A.trans _).level n = (A.trans (B.trans C)).level n
    apply Homotopy.trans_level_congr _ _ _ _ n rfl
    change (((Homotopy.precomp (a i) (K i)).trans
      (((H i).postcomp (b (i + 1))).cast (Category.assoc _ _ _) (Category.assoc _ _ _))).postcomp
        (inclusion G h (i + 1))).level n = (B.trans C).level n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl

/-- Composition of the actual track-defined telescope maps agrees through a genuine homotopy. -/
def mapOfHomotopiesCompHomotopy :
    Homotopy (mapOfHomotopies E f F g a H ≫ mapOfHomotopies F g G h b K)
      (mapOfHomotopies E f G h (fun i ↦ a i ≫ b i)
        (composeTransitionHomotopy E f F g G h a b H K)) :=
  (descRelHomotopy E f (fun i ↦ (a i ≫ b i) ≫ inclusion G h i)
    (mapCoconeCompositionRelHomotopy E f F g G h a b H K)).cast
      (by apply hom_ext; intro n i s x; rfl) rfl

/-- The actual composition comparison fixes every original included composite stage map. -/
@[simp] theorem mapOfHomotopiesCompHomotopy_inclusion
    (n i : ℕ) (r : unitInterval) (x : (E i).space n) :
    (mapOfHomotopiesCompHomotopy E f F g G h a b H K).level n
        (r, (inclusion E f i).map n x) =
      (inclusion G h i).map n ((b i).map n ((a i).map n x)) :=
  descRelHomotopy_inclusion E f _ _ n i r x

end Quillen.LoopPrespectrum.Telescope
