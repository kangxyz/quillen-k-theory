import Quillen.CategoryTheory.TheoremB.Conditions
import Quillen.CategoryTheory.TheoremA.Conclusion

/-! Theorem B's genuine transition condition is invariant under natural
isomorphisms of the original functor, with canonical transition maps retained. -/
noncomputable section
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D} (e : F ≅ G)

/-- Changing the original functor commutes with comma postcomposition. -/
def commaIsoTransitionIso {d d' : D} (f : d ⟶ d') :
    (CostructuredArrow.mapNatIso (T := d) e).functor ⋙ transition G f ≅
      transition F f ⋙ (CostructuredArrow.mapNatIso (T := d') e).functor :=
  NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _)
    (by simp [transition])) (by
    intro X Y a
    apply CostructuredArrow.hom_ext
    simp)

/-- Natural-isomorphic functors have the same actual homotopy-equivalence
condition on all comma transitions. No transition equivalence is inferred
from mere connectedness of the commas. -/
theorem transitionHomotopyEquivalences_of_natIso (e : F ≅ G)
    (h : TransitionHomotopyEquivalences F) : TransitionHomotopyEquivalences G := by
  intro d d' f
  let s := equivalenceClassifyingHomotopyEquiv (CostructuredArrow.mapNatIso (T := d) e)
  let t := (transitionHomotopyEquiv F h f).trans
    (equivalenceClassifyingHomotopyEquiv (CostructuredArrow.mapNatIso (T := d') e))
  let E := TheoremA.homotopyEquivOfTriangle s t (transitionMap G f)
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy (commaIsoTransitionIso e f).hom
      exact ⟨H.cast (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)
        (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end Quillen.TheoremB
