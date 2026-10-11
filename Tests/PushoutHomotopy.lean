/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Prespectrum.PushoutHomotopy
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare
public import Quillen.Topology.Prespectrum.StableHomotopy

/-!
Consumers of supplied relative two-parameter comparisons: equality of induced stable maps,
independent comparison/cylinder/structure coordinates, literal postcomposition, and application
to two actual homotopy-square pushout maps with identical vertex arrows.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.LoopPrespectrum.HomotopyPushout
open scoped Topology unitInterval

universe u

namespace Quillen.Tests.PushoutHomotopy

variable {A B C D E : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (b : B ⟶ D) (c : C ⟶ D)
  {H K : Homotopy (f ≫ b) (g ≫ c)} (J : H.RelHomotopy K)

include J in
lemma original_stable_maps_eq (d : ℤ) :
    (stableHomotopyFunctor d).map (desc f g b c H) =
      (stableHomotopyFunctor d).map (desc f g b c K) :=
  (descHomotopy f g b c J).stableHomotopyMap_eq d

lemma three_independent_coordinates (n : ℕ) (r s t : unitInterval) (x : A.space n) :
    (descHomotopy f g b c J).level (n + 1)
        (r, cylinder f g (n + 1) (s, A.structureMap n x t)) =
      D.structureMap n (J.level n (r, (s, x))) t := J.comm n r s x t

lemma original_postcomposition (h : D ⟶ E) (n : ℕ) (r s : unitInterval) (x : A.space n) :
    (J.postcomp h).level n (r, (s, x)) = h.map n (J.level n (r, (s, x))) := rfl

lemma constant_comparison_slice (H : Homotopy (f ≫ b) (g ≫ c)) (r : unitInterval) :
    (descHomotopy f g b c (Homotopy.RelHomotopy.refl H)).at r = desc f g b c H := by
  rw [descHomotopy_at]
  rfl

variable {A' B' C' : LoopPrespectrum.{u}}
  (f' : A' ⟶ B') (g' : A' ⟶ C') (a : A ⟶ A') (b' : B ⟶ B') (c' : C ⟶ C')
  (Hf Kf : Homotopy (f ≫ b') (a ≫ f')) (Hg Kg : Homotopy (g ≫ c') (a ≫ g'))

/-- Comparing the supplied full tracks gives an actual homotopy of their original pushout maps. -/
def compareSquareMaps
    (J : (mapSquareHomotopy f g f' g' a b' c' Hf Hg).RelHomotopy
      (mapSquareHomotopy f g f' g' a b' c' Kf Kg)) :
    Homotopy (mapOfHomotopies f g f' g' a b' c' Hf Hg)
      (mapOfHomotopies f g f' g' a b' c' Kf Kg) :=
  descHomotopy f g (b' ≫ inl f' g') (c' ≫ inr f' g') J

end Quillen.Tests.PushoutHomotopy
