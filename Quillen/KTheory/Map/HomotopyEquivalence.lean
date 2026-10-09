import Quillen.KTheory.Map.Functoriality
import Quillen.Topology.HomotopyGroups.Equivalence

/-!
# Canonical K-group maps from unbased classifying-space equivalences

The exact functor's normalized Q-functor already preserves the actual zero
basepoints. An unbased homotopy equivalence with that forward map therefore
suffices to prove its original K-map bijective in every nonnegative degree.
-/

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical zero-based K-map is bijective if the normalized Q-map is an
unbased homotopy equivalence. No based inverse homotopies are assumed. -/
theorem KMap_bijective_of_homotopyEquiv (F : ExactFunctor EC ED)
    (e : ContinuousMap.HomotopyEquiv EC.KSpace ED.KSpace)
    (he : e.toFun = (classifyingSpaceMap F.normalizedQ).hom) (n : ℕ) :
    Function.Bijective (F.KMap n) := by
  have hp : e.toFun EC.kBasepoint = ED.kBasepoint := by
    rw [he]
    exact F.normalizedQ_map_point
  simpa only [he, F.KMap_eq_piMap, ExactStructure.K, QHomotopyGroup,
    ShiftedHomotopyGroup, ExactStructure.kBasepoint] using
    piMap_bijective_of_homotopyEquiv e hp n

/-- An actual equivalence of the zero-based Quillen K-groups whose forward
homomorphism is the original exact-functor-induced map. -/
def KEquivOfHomotopyEquiv (F : ExactFunctor EC ED)
    (e : ContinuousMap.HomotopyEquiv EC.KSpace ED.KSpace)
    (he : e.toFun = (classifyingSpaceMap F.normalizedQ).hom) (n : ℕ) :
    EC.K n ≃* ED.K n :=
  MulEquiv.ofBijective (F.KMap n) (F.KMap_bijective_of_homotopyEquiv e he n)

@[simp]
theorem KEquivOfHomotopyEquiv_toMonoidHom (F : ExactFunctor EC ED)
    (e : ContinuousMap.HomotopyEquiv EC.KSpace ED.KSpace)
    (he : e.toFun = (classifyingSpaceMap F.normalizedQ).hom) (n : ℕ) :
    (F.KEquivOfHomotopyEquiv e he n).toMonoidHom = F.KMap n := rfl

end Quillen.ExactFunctor
