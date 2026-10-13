/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Prespectrum.HomotopyPushout
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
# Homotopy-pushout maps from whole homotopy squares

Maps on the three vertices of a span, together with specified coherent based homotopies for both
leg squares, induce an actual map of the reduced homotopy-pushout prespectra. Both endpoint maps
are the original supplied arrows. The entire cylinder retains, in order, the first square track,
the target overlap cylinder, and the reversed second square track.

No weak equivalence, stable cofiber comparison, or strict functor law is inferred. Even constant
square tracks introduce pauses and need not give literal equality with the strict-square map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum.HomotopyPushout

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The first square, target overlap cylinder, and reversed second square, in that order. -/
def mapSquareHomotopy :
    Homotopy (f ≫ (b ≫ inl f' g')) (g ≫ (c ≫ inr f' g')) :=
  (Hf.postcomp (inl f' g')).trans
    ((Homotopy.precomp a (glue f' g')).trans (Hg.symm.postcomp (inr f' g')))

/-- Whole homotopy-commuting leg squares give an actual map of reduced homotopy pushouts. -/
def mapOfHomotopies : prespectrum f g ⟶ prespectrum f' g' :=
  desc f g (b ≫ inl f' g') (c ≫ inr f' g')
    (mapSquareHomotopy f g f' g' a b c Hf Hg)

/-- The original left endpoint is retained literally. -/
@[simp]
theorem inl_mapOfHomotopies :
    inl f g ≫ mapOfHomotopies f g f' g' a b c Hf Hg = b ≫ inl f' g' :=
  inl_desc f g _ _ _

/-- The original right endpoint is retained literally. -/
@[simp]
theorem inr_mapOfHomotopies :
    inr f g ≫ mapOfHomotopies f g f' g' a b c Hf Hg = c ≫ inr f' g' :=
  inr_desc f g _ _ _

/-- Every point of the original overlap cylinder retains the complete supplied square tracks. -/
@[simp]
theorem mapOfHomotopies_cylinder (n : ℕ) (s : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n (cylinder f g n (s, x)) =
      (mapSquareHomotopy f g f' g' a b c Hf Hg).level n (s, x) := rfl

/-- The first half records every value of the first supplied square homotopy. -/
theorem mapOfHomotopies_first_half (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) =
      (inl f' g').map n (Hf.level n (t, x)) := by
  change (((Hf.postcomp (inl f' g')).levelHomotopy n).trans
    (((Homotopy.precomp a (glue f' g')).trans
      (Hg.symm.postcomp (inr f' g'))).levelHomotopy n)) (⟨(t : ℝ) / 2, _⟩, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change (inl f' g').map n (Hf.level n (⟨2 * ((t : ℝ) / 2), _⟩, x)) = _
    congr 2
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl
  · rename_i ht
    exfalso
    apply ht
    change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.2.2]

end Quillen.LoopPrespectrum.HomotopyPushout
