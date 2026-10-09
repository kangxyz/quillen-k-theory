import Quillen.CategoryTheory.TheoremB.Comparison
import Quillen.Topology.ClassifyingSpace.Equivalence
import Mathlib.CategoryTheory.Groupoid

/-!
# Verified sufficient conditions for the transition hypothesis

This proves the actual Theorem B hypothesis in useful categorical cases.
It does not identify the comma comparison with a homotopy equivalence.
-/

noncomputable section

open CategoryTheory
open scoped Topology

universe u

namespace Quillen.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- If every comma transition is a left adjoint, all the prescribed realized
transition maps are homotopy equivalences. -/
theorem transitionHomotopyEquivalences_of_leftAdjoints
    (h : ∀ ⦃d e : D⦄ (f : d ⟶ e), (transition F f).IsLeftAdjoint) :
    TransitionHomotopyEquivalences F := by
  intro d e f
  let := h f
  let E := adjunctionClassifyingHomotopyEquiv (Adjunction.ofIsLeftAdjoint (transition F f))
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

/-- If every comma transition is a right adjoint, the same conclusion follows
from the other orientation of the adjunction. -/
theorem transitionHomotopyEquivalences_of_rightAdjoints
    (h : ∀ ⦃d e : D⦄ (f : d ⟶ e), (transition F f).IsRightAdjoint) :
    TransitionHomotopyEquivalences F := by
  intro d e f
  let := h f
  let E := (adjunctionClassifyingHomotopyEquiv
    (Adjunction.ofIsRightAdjoint (transition F f))).symm
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

/-- An invertible target arrow gives an explicit equivalence of comma
classifying spaces with the prescribed transition as forward map. -/
def transitionHomotopyEquivOfIso {d e : D} (f : d ⟶ e) [IsIso f] :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (CostructuredArrow F d))
      (ClassifyingSpace (CostructuredArrow F e)) :=
  equivalenceClassifyingHomotopyEquiv (CostructuredArrow.mapIso (S := F) (asIso f))

@[simp]
theorem transitionHomotopyEquivOfIso_apply {d e : D} (f : d ⟶ e) [IsIso f]
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    transitionHomotopyEquivOfIso F f x = transitionMap F f x := rfl

/-- The transition condition holds for every functor into a groupoid. -/
theorem transitionHomotopyEquivalences_of_groupoid [IsGroupoid D] :
    TransitionHomotopyEquivalences F := by
  intro d e f
  let E := transitionHomotopyEquivOfIso F f
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end Quillen.TheoremB
