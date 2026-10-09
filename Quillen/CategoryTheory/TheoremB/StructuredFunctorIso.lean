import Quillen.CategoryTheory.TheoremB.FunctorIso
import Quillen.CategoryTheory.TheoremB.StructuredComparison

/-! Naturality of the genuine structured-comma transition condition under
natural isomorphisms of the original functor. -/
noncomputable section
universe u
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D}

def structuredCommaIsoTransitionIso (e : F ≅ G) {d d' : D} (f : d ⟶ d') :
    (StructuredArrow.mapNatIso (S := d') e).functor ⋙ structuredTransition G f ≅
      structuredTransition F f ⋙ (StructuredArrow.mapNatIso (S := d) e).functor :=
  NatIso.ofComponents (fun X ↦ StructuredArrow.isoMk (Iso.refl _)
    (by simp [structuredTransition])) (by
    intro X Y a
    apply StructuredArrow.hom_ext
    simp)

theorem structuredTransitionHomotopyEquivalences_of_natIso (e : F ≅ G)
    (h : StructuredTransitionHomotopyEquivalences F) :
    StructuredTransitionHomotopyEquivalences G := by
  intro d d' f
  let s := equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso (S := d') e)
  let t := (structuredTransitionHomotopyEquiv F h f).trans
    (equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso (S := d) e))
  let E := TheoremA.homotopyEquivOfTriangle s t (structuredTransitionMap G f)
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy (structuredCommaIsoTransitionIso e f).hom
      exact ⟨H.cast (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)
        (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end Quillen.TheoremB
