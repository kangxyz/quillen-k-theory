/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeMovingHomotopy
public import Quillen.Topology.Prespectrum.TelescopeHomotopyMap
public import Quillen.Topology.Prespectrum.RelativeHomotopySquare
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal

/-!
# Actual telescope homotopies from relative comparisons of supplied tracks

Relative comparisons of the whole original cocone tracks descend to a genuine
homotopy fixing every original stage. In particular, relative comparisons of
supplied transition homotopies compare their actual track-defined telescope
maps. The construction retains the comparison, cylinder, and structure times
independently and imposes no separation hypotheses.
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

/-- Relative comparisons of original cocone tracks descend through the actual telescope. -/
def descRelHomotopy {G : LoopPrespectrum.{u}} (a : ∀ i, E i ⟶ G)
    {H K : ∀ i, Homotopy (a i) (f i ≫ a (i + 1))}
    (J : ∀ i, (H i).RelHomotopy (K i)) : Homotopy (desc E f a H) (desc E f a K) :=
  descSquareHomotopy E f (fun i ↦ Homotopy.refl (a i)) (fun i ↦ (J i).toFixedSquare)

/-- The descended relative comparison retains every point of each whole supplied square. -/
@[simp] theorem descRelHomotopy_cylinder {G : LoopPrespectrum.{u}} (a : ∀ i, E i ⟶ G)
    {H K : ∀ i, Homotopy (a i) (f i ≫ a (i + 1))}
    (J : ∀ i, (H i).RelHomotopy (K i)) (k i : ℕ) (r s : unitInterval)
    (x : (E i).space k) :
    (descRelHomotopy E f a J).level k (r, cylinder E f k i (s, x)) =
      (J i).level k (r, (s, x)) := rfl

/-- Every original stage is fixed throughout the actual descended relative comparison. -/
@[simp] theorem descRelHomotopy_inclusion {G : LoopPrespectrum.{u}} (a : ∀ i, E i ⟶ G)
    {H K : ∀ i, Homotopy (a i) (f i ≫ a (i + 1))}
    (J : ∀ i, (H i).RelHomotopy (K i)) (k i : ℕ) (r : unitInterval)
    (x : (E i).space k) :
    (descRelHomotopy E f a J).level k (r, (inclusion E f i).map k x) = (a i).map k x :=
  descSquareHomotopy_inclusion E f _ _ k i r x

variable (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
  (a : ∀ i, E i ⟶ F i)
  {H K : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1))}
  (J : ∀ i, (H i).RelHomotopy (K i))

/-- The fixed target-cylinder half followed by the supplied whole relative comparison. -/
def mapCoconeRelHomotopy (i : ℕ) :
    (mapCoconeHomotopy E f F g a H i).RelHomotopy (mapCoconeHomotopy E f F g a K i) :=
  (Homotopy.RelHomotopy.refl (Homotopy.precomp (a i) (inclusionHomotopy F g i))).hcomp
    (((J i).postcomp (inclusion F g (i + 1))).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- Actual relative transition comparisons induce a genuine homotopy of the original maps. -/
def mapOfRelHomotopies :
    Homotopy (mapOfHomotopies E f F g a H) (mapOfHomotopies E f F g a K) :=
  descRelHomotopy E f (fun i ↦ a i ≫ inclusion F g i) (mapCoconeRelHomotopy E f F g a J)

/-- The actual comparison fixes the full image of each original stage map. -/
@[simp] theorem mapOfRelHomotopies_inclusion (k i : ℕ) (r : unitInterval)
    (x : (E i).space k) :
    (mapOfRelHomotopies E f F g a J).level k (r, (inclusion E f i).map k x) =
      (inclusion F g i).map k ((a i).map k x) :=
  descRelHomotopy_inclusion E f _ _ k i r x

/-- Each comparison-time slice uses precisely the supplied intermediate transition tracks. -/
theorem mapOfRelHomotopies_at (r : unitInterval) :
    (mapOfRelHomotopies E f F g a J).at r =
      mapOfHomotopies E f F g a (fun i ↦ (J i).at r) := by
  apply hom_ext
  intro k i s x
  rfl

end Quillen.LoopPrespectrum.Telescope
