/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Topology.FilteredRealization.HomotopyEquivalence
public import Quillen.Localization.Serre.FilteredComparisonAssembly

/-!
# The actual Serre quotient structured-transition homotopy equivalences

The ordinary-lift auxiliary nerves form the proved filtered simplicial
colimit of the isomorphism comma. Actual filtered realization homotopy
invariance therefore supplies the comparison equivalences. The checked
mono/epi base-change squares and quotient-span lifting then discharge all
raw structured transitions without any added quotient hypotheses.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual canonical stage map into the isomorphism-comma nerve is a
homotopy equivalence, by the proved filtered realization theorem. -/
def quotientAuxiliaryNerveStageHomotopyEquiv
    (V : Quotient P) (A : QuotientAuxiliaryLift P V) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj ((quotientAuxiliaryNerveDiagram P V).obj A))
      (SSet.toTop.obj (quotientAuxiliaryNerveCocone P V).pt) :=
  FilteredRealization.stageHomotopyEquiv (quotientAuxiliaryNerveDiagram P V)
    (quotientAuxiliaryNerveCocone P V) (quotientAuxiliaryNerveCoconeIsColimit P V)
    (quotientAuxiliaryNerveTransitionEquiv P V)
    (quotientAuxiliaryNerveTransitionEquiv_toFun P V) A

@[simp]
theorem quotientAuxiliaryNerveStageHomotopyEquiv_toFun
    (V : Quotient P) (A : QuotientAuxiliaryLift P V) :
    (quotientAuxiliaryNerveStageHomotopyEquiv P V A).toFun =
      (SSet.toTop.map ((quotientAuxiliaryNerveCocone P V).ι.app A)).hom := rfl

/-- Quillen's auxiliary comparison for every specified ordinary quotient
identification, with exactly the genuine functor as its forward map. -/
def auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv
    {N : C} {V : Quotient P} (φ : P.isoModSerre.Q.obj N ≅ V) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (IsoStructuredComma P
        (Q.of (quotientExactStructure P).deflation (quotientExactStructure P).inflation V))) := by
  let A := auxiliaryLiftMk P.isoModSerre.Q V φ
  let e := quotientAuxiliaryNerveStageHomotopyEquiv P V A
  apply TheoremA.homotopyEquivWithMap e (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P
    φ)).hom
  have he : e.toFun = (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P φ)).hom := by
    dsimp only [e, A]
    rw [quotientAuxiliaryNerveStageHomotopyEquiv_toFun, quotientAuxiliaryNerveCocone_map,
      asIso_auxiliaryLiftMk]
  rw [he]

@[simp]
theorem auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv_toFun
    {N : C} {V : Quotient P} (φ : P.isoModSerre.Q.obj N ≅ V) :
    (auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv P φ).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P φ)).hom := rfl

/-- The fixed-base auxiliary comparison is an actual map-preserving
homotopy equivalence. -/
def auxiliaryToIsoStructuredClassifyingHomotopyEquiv (N : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (IsoStructuredComma P ((quotientMapQ P).obj
        (Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation N)))) :=
  auxiliaryComparatorEquivOfFilteredStages P (quotientAuxiliaryNerveStageHomotopyEquiv P)
    (quotientAuxiliaryNerveStageHomotopyEquiv_toFun P) N

@[simp]
theorem auxiliaryToIsoStructuredClassifyingHomotopyEquiv_toFun (N : C) :
    (auxiliaryToIsoStructuredClassifyingHomotopyEquiv P N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom := rfl

/-- The canonical abelian Serre quotient satisfies every actual structured
comma transition hypothesis of Theorem B. Only the abelian and Serre-class
assumptions occur; the auxiliary comparisons are proved above. -/
theorem quotientStructuredTransitionHomotopyEquivalences :
    TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P) :=
  structuredTransitions_of_filteredAuxiliaryStages P
    (quotientAuxiliaryNerveStageHomotopyEquiv P)
    (quotientAuxiliaryNerveStageHomotopyEquiv_toFun P)

end Quillen.SerreLocalization
