/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.MixedNerves.RowCylinder
public import Quillen.Waldhausen.Fibration.MixedNerves.Realization
public import Quillen.Waldhausen.SplitComplexes.Approximation

/-! # The original mixed inclusion for genuine quotient-row cylinders

The base structural inputs are supplied by the accepted row cylinder. The
concrete complex specialization retains the original mixed nerve maps and
requires the stated cone and shift closure, with no kernel closure. As with
the generic realized theorem, object and hom universes agree here.
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

/-- The unchanged original mixed row inclusion is a genuine realization homotopy equivalence. -/
def rowChainInclusionRealizationHomotopyEquiv (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (cofChainNerve (RowWeakEquivalences.nested N n))|
      |TheoremA.diagonalSSet (coarseChainNerve (RowWeakEquivalences.nested N n))| := by
  letI : (RowWeakEquivalences.nested N n).coarse.weq.HasTwoOutOfThreeProperty :=
    RowWeakEquivalences.coarseStructure_twoOutOfThree N n
  exact chainInclusionRealizationHomotopyEquiv (RowWeakEquivalences.nested N n)
    (RowFactorization.trivialCofibrationCylinder N D hs n) (rowCylinder_fineSquares N D hs n)

@[simp] theorem rowChainInclusionRealizationHomotopyEquiv_toFun (n : SimplexCategory) :
    (rowChainInclusionRealizationHomotopyEquiv N D hs n).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (chainInclusion (RowWeakEquivalences.nested N
        n)))).hom := rfl

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The actual complex mapping cylinder discharges every generic row-cylinder input. -/
def complexRowChainInclusionRealizationHomotopyEquiv (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv
      |TheoremA.diagonalSSet (cofChainNerve (RowWeakEquivalences.nested
        (complexSubcategoryNested P) n))|
      |TheoremA.diagonalSSet (coarseChainNerve (RowWeakEquivalences.nested
        (complexSubcategoryNested P) n))| := by
  letI : (complexSubcategoryNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated P
  exact rowChainInclusionRealizationHomotopyEquiv (complexSubcategoryNested P)
    (complexJointData P hcone hshift) (complexJointData_secondEndpointSection P hcone hshift) n

@[simp] theorem complexRowChainInclusionRealizationHomotopyEquiv_toFun (n : SimplexCategory) :
    (complexRowChainInclusionRealizationHomotopyEquiv P hcone hshift n).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap
        (chainInclusion (RowWeakEquivalences.nested (complexSubcategoryNested P) n)))).hom := rfl

end Quillen.Waldhausen.Fibration.MixedNerves
