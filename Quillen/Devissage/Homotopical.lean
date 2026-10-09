import Quillen.Devissage.LayerContraction
import Quillen.Devissage.CommaLayers
import Quillen.CategoryTheory.TheoremA.ContractibleComma
import Quillen.Topology.HomotopyGroups.Equivalence

/-!
# Homotopical Quillen dévissage

For a small abelian category, the classical subobject, quotient, and
finite-product hypotheses and actual finite filtrations imply that the
canonical Q-inclusion is a homotopy equivalence. The proof identifies each
comma category with the poset of layers, contracts it by intersection and
finite-filtration induction, and applies the proved Quillen Theorem A.

Both the ordinary inclusion and its canonically zero-rebased version are
retained as exact forward maps. The all-degree K-group isomorphisms use the proved homotopy-group invariance
theorem, without assuming based inverse homotopies.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

/-- The actual inclusion comma categories are contractible under the classical
finite-filtration hypothesis. -/
theorem qComma_contractible (h : FiltrationHypothesis P) (M : C) :
    ContractibleSpace (ClassifyingSpace (QComma P M)) := by
  obtain ⟨F⟩ := h M
  let := Layer.contractible_of_filtration F
  exact (equivalenceClassifyingHomotopyEquiv (layerCommaEquivalence P M)).symm.contractibleSpace

/-- Classical Quillen dévissage, with the canonical realized Q-inclusion as
the forward map. No extension closure or uniform filtration bound is assumed. -/
def classifyingHomotopyEquiv (h : FiltrationHypothesis P) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Q (subcategoryExactStructure P).deflation
        (subcategoryExactStructure P).inflation))
      (ClassifyingSpace (Q (abelianExactStructure C).deflation
        (abelianExactStructure C).inflation)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (mapQ P)
    (fun M => qComma_contractible P h M.obj.of)

@[simp]
theorem classifyingHomotopyEquiv_toFun (h : FiltrationHypothesis P) :
    (classifyingHomotopyEquiv P h).toFun = (classifyingSpaceMap (mapQ P)).hom := rfl

/-- The actual pointed continuous map used in the project's inclusion-induced
Quillen K-group homomorphisms. -/
def pointedClassifyingMap :=
  (classifyingSpaceMap (rebaseFunctor (mapQ P)
    (Q.of (subcategoryExactStructure P).deflation
      (subcategoryExactStructure P).inflation (0 : Subcategory P))
    (Q.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation (0 : C))
    ((abelianExactStructure C).qIsoOfIso (exactInclusion P).toFunctor.mapZeroObject))).hom

/-- Rebasing at the chosen zero object preserves the proved equivalence.
Its forward map is precisely the one defining `Devissage.KMap`. -/
def pointedClassifyingHomotopyEquiv (h : FiltrationHypothesis P) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Q (subcategoryExactStructure P).deflation
        (subcategoryExactStructure P).inflation))
      (ClassifyingSpace (Q (abelianExactStructure C).deflation
        (abelianExactStructure C).inflation)) :=
  TheoremA.homotopyEquivWithMap (classifyingHomotopyEquiv P h)
    (pointedClassifyingMap P)
    ⟨classifyingSpaceNaturalTransformationHomotopy
      (rebaseFunctorIso (mapQ P)
        (Q.of (subcategoryExactStructure P).deflation
          (subcategoryExactStructure P).inflation (0 : Subcategory P))
        (Q.of (abelianExactStructure C).deflation
          (abelianExactStructure C).inflation (0 : C))
        ((abelianExactStructure C).qIsoOfIso (exactInclusion P).toFunctor.mapZeroObject)).inv⟩

@[simp]
theorem pointedClassifyingHomotopyEquiv_toFun (h : FiltrationHypothesis P) :
    (pointedClassifyingHomotopyEquiv P h).toFun = pointedClassifyingMap P := rfl


/-- The canonical rebased inclusion preserves the actual K-theory basepoints. -/
lemma pointedClassifyingMap_basepoint :
    pointedClassifyingMap P (subcategoryExactStructure P).kBasepoint =
      (abelianExactStructure C).kBasepoint :=
  rebaseFunctor_map_point (mapQ P) _ _ _

/-- Classical dévissage on every nonnegative Quillen K-group. The inverse is
obtained from the proved homotopy equivalence, not postulated as filtration data. -/
def KEquiv (h : FiltrationHypothesis P) (n : ℕ) :
    (subcategoryExactStructure P).K n ≃* (abelianExactStructure C).K n :=
  homotopyEquivPiEquiv (pointedClassifyingHomotopyEquiv P h)
    (pointedClassifyingMap_basepoint P) n

/-- The forward homomorphism of dévissage is exactly the already-defined
inclusion-induced K-map, including its canonical zero-object rebasing. -/
@[simp]
theorem KEquiv_toMonoidHom (h : FiltrationHypothesis P) (n : ℕ) :
    (KEquiv P h n).toMonoidHom = KMap P n := rfl

/-- In particular the canonical inclusion-induced map is bijective in every
degree, including `K₀ = π₁ BQ`. -/
theorem KMap_bijective (h : FiltrationHypothesis P) (n : ℕ) :
    Function.Bijective (KMap P n) := (KEquiv P h n).bijective

end Quillen.Devissage
