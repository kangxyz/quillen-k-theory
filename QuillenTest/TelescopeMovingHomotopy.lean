/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeRelativeHomotopy
import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-!
# Actual original-telescope homotopy consumers

Restricting a descended moving-square homotopy along an original stage inclusion
recovers the whole supplied stage homotopy. An actual terminal stutter in every
original cylinder is removed by a genuine prespectrum homotopy, with no
separation or compactness hypotheses.
-/

open CategoryTheory
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeMovingHomotopy

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- Restriction along an original stage preserves the entire supplied moving homotopy. -/
theorem original_stage_homotopy {G : LoopPrespectrum.{u}} {a b : ∀ i, E i ⟶ G}
    {H : ∀ i, Homotopy (a i) (f i ≫ a (i + 1))}
    {K : ∀ i, Homotopy (b i) (f i ≫ b (i + 1))}
    (L : ∀ i, Homotopy (a i) (b i))
    (S : ∀ i, (H i).Square (K i) (L i) (Homotopy.precomp (f i) (L (i + 1)))) (i : ℕ) :
    ((Homotopy.precomp (Telescope.inclusion E f i)
      (Telescope.descSquareHomotopy E f L S)).cast
        (Telescope.inclusion_desc E f a H i) (Telescope.inclusion_desc E f b K i)) = L i := by
  apply Homotopy.ext
  funext k
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  exact Telescope.descSquareHomotopy_inclusion E f L S k i r x

/-- Removing every original cylinder's terminal constant half is a genuine homotopy to identity. -/
noncomputable def originalStutterRemoval :
    Homotopy
      (Telescope.desc E f (Telescope.inclusion E f)
        (fun i ↦ (Telescope.inclusionHomotopy E f i).trans
          (Homotopy.refl (f i ≫ Telescope.inclusion E f (i + 1)))))
      (𝟙 (Telescope.prespectrum E f)) :=
  (Telescope.descRelHomotopy E f (Telescope.inclusion E f)
    (fun i ↦ Homotopy.RelHomotopy.transRefl (Telescope.inclusionHomotopy E f i))).cast rfl (by
      apply Telescope.hom_ext
      intro k i s x
      rfl)

/-- The actual stutter-removal homotopy fixes every point of every original stage. -/
theorem originalStutterRemoval_fixes_stage (k i : ℕ) (r : unitInterval)
    (x : (E i).space k) :
    (originalStutterRemoval E f).level k (r, (Telescope.inclusion E f i).map k x) =
      (Telescope.inclusion E f i).map k x :=
  Telescope.descRelHomotopy_inclusion E f _ _ k i r x

/-- Three-quarter cylinder time samples the actual supplied relative comparison at half time. -/
theorem supplied_transition_square_midpoint
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i)
    {H K : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1))}
    (J : ∀ i, (H i).RelHomotopy (K i)) (k i : ℕ) (r : unitInterval)
    (x : (E i).space k) :
    (Telescope.mapOfRelHomotopies E f F g a J).level k
        (r, Telescope.cylinder E f k i (⟨3 / 4, by constructor <;> norm_num⟩, x)) =
      (Telescope.inclusion F g (i + 1)).map k
        ((J i).level k (r, (⟨1 / 2, by constructor <;> norm_num⟩, x))) := by
  have ht := congrArg
    (fun q : Telescope.prespectrum E f ⟶ Telescope.prespectrum F g ↦
      q.map k (Telescope.cylinder E f k i (⟨3 / 4, by constructor <;> norm_num⟩, x)))
    (Telescope.mapOfRelHomotopies_at E f F g a J r)
  have hs := Telescope.mapOfHomotopies_second_half E f F g a (fun j ↦ (J j).at r) k i
    ⟨3 / 4, by constructor <;> norm_num⟩ (by norm_num) x
  have he : (⟨2 * (3 / 4) - 1, by constructor <;> norm_num⟩ : unitInterval) =
      ⟨1 / 2, by constructor <;> norm_num⟩ := by ext; norm_num
  exact ht.trans (by simpa only [he, Homotopy.RelHomotopy.at, ContinuousMap.coe_mk] using hs)

end QuillenTest.TelescopeMovingHomotopy
