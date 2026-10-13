/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.Limits.SequentialExactness
public import Quillen.Topology.Prespectrum.TelescopeHomotopyMapStable

/-!
# Stable exactness of the original telescope maps

The actual telescope maps determined by whole transition homotopies retain
stagewise exactness on the original signed stable groups. The proof uses the
canonical comparison isomorphisms and exactness of sequential abelian-group
colimits. Exactness of the stage maps is an explicit hypothesis; in particular,
this does not assume or establish a stable mapping-cone exactness theorem.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
  (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
  (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
  (H : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1)))
  (K : ∀ i, Homotopy (b i ≫ h i) (g i ≫ b (i + 1)))
  [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]
  [∀ i k, T1Space ((G i).space k)]

/-- Genuine stagewise stable exactness passes to the actual maps with supplied transition tracks. -/
theorem mapOfHomotopies_stable_exact (d : ℤ)
    (hex : ∀ i, Function.Exact ((stableHomotopyFunctor d).map (a i))
      ((stableHomotopyFunctor d).map (b i))) :
    Function.Exact ((stableHomotopyFunctor d).map (mapOfHomotopies E f F g a H))
      ((stableHomotopyFunctor d).map (mapOfHomotopies F g G h b K)) := by
  let α := homotopyStageStableDiagramMap E f F g a H d
  let β := homotopyStageStableDiagramMap F g G h b K d
  have hex' : Function.Exact (colimMap α) (colimMap β) :=
    sequentialColimit_exact α β hex
  apply (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (colimMap α).hom (colimMap β).hom
    ((stableHomotopyFunctor d).map (mapOfHomotopies E f F g a H)).hom
    ((stableHomotopyFunctor d).map (mapOfHomotopies F g G h b K)).hom
    (stableColimitComparison E f d).hom (stableColimitComparison F g d).hom
    (stableColimitComparison G h d).hom ?_ ?_
    (ConcreteCategory.bijective_of_isIso (stableColimitComparison E f d)).2
    (ConcreteCategory.bijective_of_isIso (stableColimitComparison F g d))
    (ConcreteCategory.bijective_of_isIso (stableColimitComparison G h d)).1).mp hex'
  · exact congrArg AddCommGrpCat.Hom.hom
      (stableColimitComparison_mapOfHomotopies E f F g a H d).symm
  · exact congrArg AddCommGrpCat.Hom.hom
      (stableColimitComparison_mapOfHomotopies F g G h b K d).symm

end Quillen.LoopPrespectrum.Telescope
