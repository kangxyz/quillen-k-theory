import Quillen.CategoryTheory.TheoremA.ContractibleComma
import Quillen.Topology.HomotopyGroups.Equivalence

/-!
# The canonical homotopy-group isomorphisms in Quillen's Theorem A

Contractible comma classifying spaces suffice for the actual map induced by
the functor to be an isomorphism in every positive homotopy degree, at every
object vertex. No based inverse or fixed-point homotopies are hypothesized.
-/

noncomputable section
universe u
open CategoryTheory

namespace Quillen.TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The canonical shifted homotopy-group map is bijective under the genuine
contractible-comma hypothesis of Theorem A. -/
theorem shiftedHomotopyGroupMap_bijective_of_contractibleComma
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d)))
    (c : C) (n : ℕ) : Function.Bijective (shiftedHomotopyGroupMap F c n) :=
  piMap_bijective_of_homotopyEquiv (contractibleCommaClassifyingHomotopyEquiv F h)
    (classifyingSpaceMap_point F c) n

/-- Theorem A as a genuine isomorphism of the actual positive homotopy groups,
with precisely the functor-induced homomorphism as its forward map. -/
def contractibleCommaShiftedHomotopyEquiv
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d)))
    (c : C) (n : ℕ) :
    ShiftedHomotopyGroup C c n ≃* ShiftedHomotopyGroup D (F.obj c) n :=
  homotopyEquivPiEquiv (contractibleCommaClassifyingHomotopyEquiv F h)
    (classifyingSpaceMap_point F c) n

@[simp]
theorem contractibleCommaShiftedHomotopyEquiv_toMonoidHom
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d)))
    (c : C) (n : ℕ) :
    (contractibleCommaShiftedHomotopyEquiv F h c n).toMonoidHom =
      shiftedHomotopyGroupMap F c n := rfl

end Quillen.TheoremA
