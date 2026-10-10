/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.MixedNerves.RowPostcompose
public import Quillen.Waldhausen.Fibration.MixedNerves.RowRealization
public import Quillen.Waldhausen.SplitComplexes.Approximation

/-! # The original total mixed inclusion for genuine inner quotient rows

The third-index map is the original quotient-row restriction, and every
row comparison is the checked original mixed inclusion. The proved
bisimplicial realization theorem therefore totalizes these actual forward
maps. No naturality of the chosen row homotopy inverses is required.
-/
@[expose] public section

noncomputable section
open CategoryTheory CochainComplex
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)
  [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- Genuine total realization equivalence with the original three-index inclusion forward. -/
def totalChainInclusionRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (cofRowDiagonals N)|
      |TheoremA.diagonalSSet (coarseRowDiagonals N)| :=
  BisimplicialRealization.diagonalRealizationHomotopyEquiv (rowDiagonalInclusion N)
    (fun n ↦ rowChainInclusionRealizationHomotopyEquiv N D hs ⦋n⦌)
    (fun n ↦ rowChainInclusionRealizationHomotopyEquiv_toFun N D hs ⦋n⦌)

@[simp] theorem totalChainInclusionRealizationHomotopyEquiv_toFun :
    (totalChainInclusionRealizationHomotopyEquiv N D hs).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (rowDiagonalInclusion N))).hom := rfl

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The actual complex cylinder supplies the genuine total mixed-inclusion equivalence. -/
def complexTotalChainInclusionRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (cofRowDiagonals
      (complexSubcategoryNested P))|
      |TheoremA.diagonalSSet (coarseRowDiagonals (complexSubcategoryNested P))| := by
  letI : (complexSubcategoryNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated P
  exact totalChainInclusionRealizationHomotopyEquiv (complexSubcategoryNested P)
    (complexJointData P hcone hshift) (complexJointData_secondEndpointSection P hcone hshift)

@[simp] theorem complexTotalChainInclusionRealizationHomotopyEquiv_toFun :
    (complexTotalChainInclusionRealizationHomotopyEquiv P hcone hshift).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (rowDiagonalInclusion (complexSubcategoryNested
        P)))).hom := rfl

end Quillen.Waldhausen.Fibration.MixedNerves
