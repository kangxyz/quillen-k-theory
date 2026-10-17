/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.Comma.Transitions
public import Quillen.CategoryTheory.TheoremB.FunctorIso
public import Quillen.CategoryTheory.TheoremB.StructuredComparison

/-! Naturality of the genuine structured-comma transition condition under
natural isomorphisms of the original functor. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D}

theorem structuredTransitionHomotopyEquivalences_of_natIso (e : F ≅ G)
    (h : StructuredTransitionHomotopyEquivalences F) :
    StructuredTransitionHomotopyEquivalences G := by
  intro d d' f
  let s := equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso (S := d') e)
  let t := (structuredTransitionHomotopyEquiv F h f).trans
    (equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso (S := d) e))
  let E := TheoremA.homotopyEquivOfTriangle s t (structuredTransitionMap G f)
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy (structuredCommaIsoTransitionIso e
        f).hom
      exact ⟨H.cast (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)
        (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end Quillen.TheoremB
