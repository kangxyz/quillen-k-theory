/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Localization.Serre.AuxiliaryColimit
public import Quillen.Localization.Serre.StructuredTransitionAssembly

/-!
# Exact-map assembly from filtered stage equivalences to localization transitions

This adapter records only the final substitution step. Actual homotopy
invariance of the filtered realization must supply the displayed stage
homotopy equivalences; finite-homotopy bijectivity is not substituted for them.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]
variable
  (E : ∀ (V : Quotient P) (A : QuotientAuxiliaryLift P V),
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj ((quotientAuxiliaryNerveDiagram P V).obj A))
      (SSet.toTop.obj (quotientAuxiliaryNerveCocone P V).pt))
  (hE : ∀ V A, (E V A).toFun =
    (SSet.toTop.map ((quotientAuxiliaryNerveCocone P V).ι.app A)).hom)

/-- The identity ordinary lift gives the fixed-base comparator, retaining
that exact functor's realization as the forward map. -/
def auxiliaryComparatorEquivOfFilteredStages
    (hE : ∀ V A, (E V A).toFun =
      (SSet.toTop.map ((quotientAuxiliaryNerveCocone P V).ι.app A)).hom) (N : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (IsoStructuredComma P ((quotientMapQ P).obj
        (Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation N)))) := by
  let A := auxiliaryLiftMk P.isoModSerre.Q (P.isoModSerre.Q.obj N) (Iso.refl _)
  let e := E (P.isoModSerre.Q.obj N) A
  have he : e.toFun = (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom := by
    dsimp only [e, A]
    rw [hE, quotientAuxiliaryNerveCocone_map]
    calc
      _ = (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P
          (Iso.refl (P.isoModSerre.Q.obj N)))).hom :=
        congrArg (fun φ : P.isoModSerre.Q.obj N ≅ P.isoModSerre.Q.obj N =>
          (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P φ)).hom)
          (asIso_auxiliaryLiftMk P _ N (Iso.refl _))
      _ = _ := congrArg (fun F => (classifyingSpaceMap F).hom)
        (auxiliaryToIsoStructured_eq_withBaseRefl P N).symm
  apply TheoremA.homotopyEquivWithMap e (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom
  rw [he]

@[simp]
theorem auxiliaryComparatorEquivOfFilteredStages_toFun (N : C) :
    (auxiliaryComparatorEquivOfFilteredStages P E hE N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom := rfl

include hE

/-- The checked mono/epi squares and quotient-arrow lifting complete every
raw structured transition once actual filtered stage equivalences are supplied. -/
theorem structuredTransitions_of_filteredAuxiliaryStages :
    TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P) :=
  structuredTransitions_of_auxiliaryComparatorEquivalences P
    (auxiliaryComparatorEquivOfFilteredStages P E hE)
    (auxiliaryComparatorEquivOfFilteredStages_toFun P E hE)

end Quillen.SerreLocalization
