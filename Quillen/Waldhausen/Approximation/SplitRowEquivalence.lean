/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Approximation.FlagRowEquivalence
public import Quillen.Waldhausen.SplitComplexes.Approximation
public import Quillen.Waldhausen.SplitComplexes.FunctorialFactorization

/-!
# Change of cofibrations on actual quasi-isomorphism row categories

The canonical inclusion from degreewise-split rows to ambient-cofibration
rows induces an actual homotopy equivalence. Its inverse is built from
initial flags, functorial identity-cone replacement, and canonical quotient
completion. Only proved closure properties of the complex subcategory enter.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped Simplicial

universe v u

namespace Quillen.Waldhausen

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The actual exact structure furnishing the quotient rows. -/
abbrev complexSubcategoryExact :=
  ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) P

/-- The canonical change of cofibrations on actual quasi-isomorphism rows. -/
def splitRowInclusion (n : SimplexCategory) :
    WeakRow (complexSubcategoryExact P) (splitComplexSubcategory P).cof
      (complexSubcategory P).weq n ⥤
    WeakRow (complexSubcategoryExact P) (complexSubcategory P).cof
      (complexSubcategory P).weq n :=
  WeakRow.inclusion _ (fun _ _ _ h ↦ h.1)

variable (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
  ∀ f : K ⟶ L, P (mappingCone f)) (n : SimplexCategory)

/-- The explicit composite through finite flags, prior to straightening its
forward map to the canonical row inclusion. -/
def splitRowCompositeHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (WeakRow (complexSubcategoryExact P) (splitComplexSubcategory P).cof
        (complexSubcategory P).weq n))
      (ClassifyingSpace (WeakRow (complexSubcategoryExact P) (complexSubcategory P).cof
        (complexSubcategory P).weq n)) := by
  letI := splitComplexSubcategory_saturated P
  exact ((rowInitialFlagClassifyingHomotopyEquiv (complexSubcategoryExact P)
    (splitComplexSubcategory P) (complexSubcategory P) (fun _ _ _ h ↦ h.1) (fun _ _ _ h ↦ h)
      n).trans
      (FunctorialFactorization.flagInclusionClassifyingHomotopyEquiv
        (splitSubcategoryFunctorialFactorization P hcone) (complexSubcategory P).cof n.len
          (fun _ _ _ h ↦ h.1))).trans
    (rowInitialFlagClassifyingHomotopyEquiv (complexSubcategoryExact P)
      (complexSubcategory P) (complexSubcategory P) (fun _ _ _ h ↦ h) (fun _ _ _ h ↦ h) n).symm

/-- The quotient presentation naturally identifies the composite forward map
with the canonical inclusion. -/
def splitRowCompositeHomotopy :
    (splitRowCompositeHomotopyEquiv P hcone n).toFun.Homotopy
      (classifyingSpaceMap (splitRowInclusion P n)).hom := by
  let I := WeakFlag.inclusion (cof := (splitComplexSubcategory P).cof)
    (weq := (complexSubcategory P).weq) (n := n.len)
    (complexSubcategory P).cof (fun _ _ _ h ↦ h.1)
  let R := completeFlags (complexSubcategoryExact P) (complexSubcategory P)
    (complexSubcategory P) (fun _ _ _ h ↦ h) (fun _ _ _ h ↦ h) (n := n)
  have hfun : WeakRow.initialFlagFunctor ⋙ I =
      splitRowInclusion P n ⋙ WeakRow.initialFlagFunctor := rfl
  have hh := congrArg (fun F ↦ (classifyingSpaceMap F).hom) hfun
  simp only [classifyingSpaceMap_comp, TopCat.hom_comp] at hh
  change ((classifyingSpaceMap R).hom.comp
    ((classifyingSpaceMap I).hom.comp
      (classifyingSpaceMap WeakRow.initialFlagFunctor).hom)).Homotopy _
  rw [hh]
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp, ContinuousMap.id_comp, ContinuousMap.comp_assoc] using
      classifyingSpaceNaturalTransformationHomotopy
        (Functor.whiskerLeft (splitRowInclusion P n)
          (rowCompletionCounit (complexSubcategoryExact P) (complexSubcategory P)
            (complexSubcategory P) (fun _ _ _ h ↦ h) (fun _ _ _ h ↦ h) n))

/-- The actual canonical inclusion of the quasi-isomorphism row categories
is a homotopy equivalence. No approximation conclusion is assumed. -/
def splitRowInclusionClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (WeakRow (complexSubcategoryExact P) (splitComplexSubcategory P).cof
        (complexSubcategory P).weq n))
      (ClassifyingSpace (WeakRow (complexSubcategoryExact P) (complexSubcategory P).cof
        (complexSubcategory P).weq n)) where
  toFun := (classifyingSpaceMap (splitRowInclusion P n)).hom
  invFun := (splitRowCompositeHomotopyEquiv P hcone n).invFun
  left_inv := ⟨((ContinuousMap.Homotopy.refl _).comp
    (splitRowCompositeHomotopy P hcone n).symm).trans
      (splitRowCompositeHomotopyEquiv P hcone n).left_inv.some⟩
  right_inv := ⟨((splitRowCompositeHomotopy P hcone n).symm.compContinuousMap _).trans
    (splitRowCompositeHomotopyEquiv P hcone n).right_inv.some⟩

@[simp]
theorem splitRowInclusionClassifyingHomotopyEquiv_toFun :
    (splitRowInclusionClassifyingHomotopyEquiv P hcone n).toFun =
      (classifyingSpaceMap (splitRowInclusion P n)).hom := rfl

end Quillen.Waldhausen
