/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeRelativeHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# The actual identity homotopy for track-defined telescope maps

The canonical constant transition tracks for identity stage maps give a
stuttered original cylinder. Removing its terminal constant half yields a
genuine based prespectrum homotopy to the original identity map. Every original
stage stays fixed. Arbitrary identity tracks are not asserted to admit this
homotopy without relative comparison data.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The original constant transition homotopy for identity stage maps. -/
def identityTransitionHomotopy (i : ℕ) :
    Homotopy (𝟙 (E i) ≫ f i) (f i ≫ 𝟙 (E (i + 1))) :=
  (Homotopy.refl (f i)).cast (Category.id_comp _).symm (Category.comp_id _).symm

/-- Remove the actual terminal constant half of the identity-map cocone track. -/
def identityMapCoconeRelHomotopy (i : ℕ) :
    (mapCoconeHomotopy E f E f (fun j ↦ 𝟙 (E j)) (identityTransitionHomotopy E f) i).RelHomotopy
      ((inclusionHomotopy E f i).cast (Category.id_comp _).symm
        (by simp only [Category.id_comp])) := by
  apply (Homotopy.RelHomotopy.transRefl (inclusionHomotopy E f i)).ofLevels
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rfl

/-- Canonical identity tracks give a genuine homotopy to the original telescope identity. -/
def mapOfHomotopiesIdHomotopy :
    Homotopy (mapOfHomotopies E f E f (fun i ↦ 𝟙 (E i)) (identityTransitionHomotopy E f))
      (𝟙 (prespectrum E f)) :=
  (descRelHomotopy E f (fun i ↦ 𝟙 (E i) ≫ inclusion E f i)
    (identityMapCoconeRelHomotopy E f)).cast rfl
      (by apply hom_ext; intro n i s x; rfl)

/-- The genuine identity comparison fixes every original stage point throughout. -/
@[simp] theorem mapOfHomotopiesIdHomotopy_inclusion
    (n i : ℕ) (r : unitInterval) (x : (E i).space n) :
    (mapOfHomotopiesIdHomotopy E f).level n (r, (inclusion E f i).map n x) =
      (inclusion E f i).map n x :=
  descRelHomotopy_inclusion E f _ _ n i r x

end Quillen.LoopPrespectrum.Telescope
