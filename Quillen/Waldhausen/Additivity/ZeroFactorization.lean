/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Additivity.CofibrationSequence

/-! # Disjoint interval maps are the actual canonical zero maps -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
universe u v

namespace Quillen.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- Every composite through any genuine zero object is the canonical zero
map through the chosen Waldhausen zero. -/
theorem comp_through_isZero {X Z Y : C} (hZ : IsZero Z) (f : X ⟶ Z) (g : Z ⟶ Y) :
    f ≫ g = zeroMorphism V X Y := by
  rw [hZ.eq_of_src g (V.isZero.from_ Z ≫ V.isZero.to_ Y), ← Category.assoc,
    V.isZero.eq_of_tgt (f ≫ V.isZero.from_ Z) (V.isZero.from_ X)]
  rfl

/-- A map between disjoint ordered intervals factors through the actual zero
diagonal, hence is zero without any preadditive structure. -/
theorem intervalMap_eq_zero {n : SimplexCategory} (A : Interval n ⥤ C)
    (hA : ∀ i, IsZero (A.obj (interval i i le_rfl)))
    (i j k l : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    A.map (homOfLE (show interval i j hij ≤ interval k l hkl from
      ⟨hij.trans hjk, hjk.trans hkl⟩)) =
      zeroMorphism V (A.obj (interval i j hij)) (A.obj (interval k l hkl)) := by
  have he : (homOfLE (show interval i j hij ≤ interval j j le_rfl from ⟨hij, le_rfl⟩)) ≫
      homOfLE (show interval j j le_rfl ≤ interval k l hkl from ⟨hjk, hjk.trans hkl⟩) =
      homOfLE (show interval i j hij ≤ interval k l hkl from ⟨hij.trans hjk, hjk.trans hkl⟩) :=
    Subsingleton.elim _ _
  rw [← he, A.map_comp]
  exact comp_through_isZero V (hA j) _ _

end Quillen.Waldhausen.Additivity
