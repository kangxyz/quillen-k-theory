import Quillen.Waldhausen.Fibration.RelativeRows.CoarseEvaluation
import Quillen.Waldhausen.Fibration.ComplexExtension
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.GilletWaldhausen
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace BoundedTermsRelativeCoarseConsumer
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- Only the original term-subcategory hypotheses; all cylinder/section/extension
inputs are the actual already proved bounded-complex constructions. -/
def actualEquiv :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (RelativeRows.relativeSRows (boundedTermsNested P))|
      |sSet (boundedTermsNested P).coarse.cof (boundedTermsNested P).coarse.weq| := by
  letI : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact RelativeRows.coarseEvaluationHomotopyEquiv (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))

/-- The consumer retains the exact original relative-to-coarse S-map. -/
example : (actualEquiv P).toFun =
    (SSet.toTop.map (RelativeRows.coarseEvaluation (boundedTermsNested P)
      (complexSubcategory_extensionAxiom (boundedTerms P)))).hom := by
  let : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact RelativeRows.coarseEvaluationHomotopyEquiv_toFun (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))

#print axioms actualEquiv
end BoundedTermsRelativeCoarseConsumer
