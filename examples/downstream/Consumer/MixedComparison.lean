import Quillen.Library

/-! Actual original-model comparisons consumed through the public library. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.Fibration.RelativeRows
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Consumer.MixedComparison
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)

def originalRelativeFiltrationEquiv :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (relativeSRows N)|
      |TheoremA.diagonalSSet (MixedNerves.cofRowDiagonals N)| :=
  relativeFiltrationTotalHomotopyEquiv N he

theorem originalRelativeFiltration_forward : (originalRelativeFiltrationEquiv N he).toFun =
    (SSet.toTop.map (relativeFiltrationTotalMap N he)).hom := relativeFiltrationTotalHomotopyEquiv_toFun N he

def originalCoarseEvaluationEquiv :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (MixedNerves.coarseRowDiagonals N)|
      |sSet N.coarse.cof N.coarse.weq| := MixedNerves.totalCoarseEvaluationHomotopyEquiv N

theorem originalCoarseEvaluation_forward : (originalCoarseEvaluationEquiv N).toFun =
    (SSet.toTop.map (MixedNerves.totalCoarseEvaluation N)).hom :=
  MixedNerves.totalCoarseEvaluationHomotopyEquiv_toFun N

theorem original_canonical_triangle : totalFiberInclusion N ≫ coarseEvaluation N he =
    sSetMap (changeWeak_exact N) := totalFiberInclusion_coarseEvaluation N he

theorem original_realized_triangle : (SSet.toTop.map (coarseEvaluation N he)).hom.comp
    (SSet.toTop.map (totalFiberInclusion N)).hom = changeWeakMap N :=
  totalFiberInclusion_coarseEvaluation_realized N he

theorem original_evaluation_basepoint : SSet.toTop.map (coarseEvaluation N he)
    (totalBasepoint N) = N.coarse.kBasepoint := coarseEvaluation_basepoint N he

theorem original_fiber_basepoint : SSet.toTop.map (totalFiberInclusion N)
    V.kBasepoint = totalBasepoint N := totalFiberInclusion_basepoint N

variable (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]
def originalRelativeCoarseEquiv :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (relativeSRows N)|
      |sSet N.coarse.cof N.coarse.weq| := coarseEvaluationHomotopyEquiv N he D hs

theorem originalRelativeCoarse_forward : (originalRelativeCoarseEquiv N he D hs).toFun =
    (SSet.toTop.map (coarseEvaluation N he)).hom := coarseEvaluationHomotopyEquiv_toFun N he D hs
end Consumer.MixedComparison

namespace Consumer.BoundedTermsMixedComparison
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

def originalRelativeCoarseEquiv : ContinuousMap.HomotopyEquiv
    |TheoremA.diagonalSSet (relativeSRows (boundedTermsNested P))|
    |sSet (boundedTermsNested P).coarse.cof (boundedTermsNested P).coarse.weq| := by
  letI : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact coarseEvaluationHomotopyEquiv (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ hK ↦ boundedTerms_shift P hK 1))
end Consumer.BoundedTermsMixedComparison
