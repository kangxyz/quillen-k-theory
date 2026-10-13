/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Prespectrum.PushoutHomotopySquare

/-!
Semantic consumers for whole-square pushout maps: both literal endpoint arrows, independent
cylinder/structure coordinates, and the original first-square midpoint rather than a substituted
endpoint-only track.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.LoopPrespectrum.HomotopyPushout
open scoped Topology unitInterval

universe u

namespace QuillenTest.PushoutHomotopySquare

open Quillen

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

lemma original_endpoint_points (n : ℕ) (y : B.space n) (z : C.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n ((inl f g).map n y) =
        (inl f' g').map n (b.map n y) ∧
      (mapOfHomotopies f g f' g' a b c Hf Hg).map n ((inr f g).map n z) =
        (inr f' g').map n (c.map n z) :=
  ⟨congrArg (fun h ↦ h.map n y) (inl_mapOfHomotopies f g f' g' a b c Hf Hg),
    congrArg (fun h ↦ h.map n z) (inr_mapOfHomotopies f g f' g' a b c Hf Hg)⟩

lemma independent_structure_coordinate (n : ℕ) (s t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map (n + 1)
        (cylinder f g (n + 1) (s, A.structureMap n x t)) =
      (prespectrum f' g').structureMap n
        ((mapOfHomotopies f g f' g' a b c Hf Hg).map n (cylinder f g n (s, x))) t :=
  congrArg (fun p ↦ p t) ((mapOfHomotopies f g f' g' a b c Hf Hg).comm n
    (cylinder f g n (s, x)))

lemma first_square_midpoint (n : ℕ) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (⟨(1 : ℝ) / 4, by constructor <;> norm_num⟩, x)) =
      (inl f' g').map n (Hf.level n (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩, x)) := by
  convert mapOfHomotopies_first_half f g f' g' a b c Hf Hg n
    ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ x using 1
  congr 1
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    norm_num
  · rfl

end QuillenTest.PushoutHomotopySquare
