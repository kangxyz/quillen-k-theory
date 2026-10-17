/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.ExactCategory.Resolution.Closure
public import Quillen.Resolution.Finite

/-! # K-theory applications of resolving closure -/
@[expose] public section
open CategoryTheory.ExactCategory
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Resolution
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The canonical inclusion-induced K-group map. No bijectivity is built into
its type or its data. -/
abbrev inclusionKMap (n : ℕ) := (exactInclusion E P).KMap n

/-- Finite resolutions give algebraic Grothendieck surjectivity without any
homotopical assumption. -/
theorem grothendieckMap_surjective (h : E.ResolutionHypothesis P) :
    Function.Surjective (exactInclusion E P).grothendieckMap := by
  apply AddMonoidHom.range_eq_top.mp
  apply CategoryTheory.ExactCategory.ExactStructure.grothendieckSubgroup_eq_top_of_classes
  intro X
  obtain ⟨R⟩ := h X
  apply R.class_mem
  intro Y hY
  exact ⟨(ExactSubcategory.exactStructure E P).grothendieckClass ⟨Y, hY⟩,
    (exactInclusion E P).grothendieckMap_class ⟨Y, hY⟩⟩

end Quillen.Resolution
