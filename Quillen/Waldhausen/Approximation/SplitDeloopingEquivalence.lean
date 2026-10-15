/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.Approximation.SplitRowEquivalence
public import Quillen.Waldhausen.Approximation.WeakRowDiagonal
public import Quillen.Topology.Realization.BisimplicialEquivalence

/-!
# The actual change-of-cofibrations equivalence on S-construction realizations

The row equivalences were built from actual finite factorization and actual
cokernel completion. The proved bisimplicial invariance theorem now yields
an equivalence on the original S-grid realization with exactly the canonical
identity comparison as forward map.
-/
@[expose] public section

open CategoryTheory.ExactCategory



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
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

/-- The strictly simplicial canonical comparison on the actual row nerves. -/
def splitRowNerveInclusion :=
  weakRowNerveInclusion (complexSubcategoryExact P)
    (splitComplexSubcategory P).cof (complexSubcategory P).weq
    (complexSubcategory P).cof (fun _ _ _ h ↦ h.1)

/-- Actual rowwise homotopy equivalences induce the diagonal realization
equivalence without requiring any compatible choice of rowwise inverses. -/
def splitRowDiagonalHomotopyEquiv :=
  BisimplicialRealization.diagonalRealizationHomotopyEquiv
    (splitRowNerveInclusion P)
    (fun n ↦ splitRowInclusionClassifyingHomotopyEquiv P hcone ⦋n⦌)
    (fun _ ↦ rfl)

/-- The actual S-construction realizations for split and ambient
cofibrations are homotopy equivalent. -/
def splitDeloopingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (splitComplexSubcategory P).Delooping
      (complexSubcategory P).Delooping :=
  ((TopCat.homeoOfIso (SSet.toTop.mapIso
    (weakRowDiagonalIso (complexSubcategoryExact P) (splitComplexSubcategory P).cof
      (complexSubcategory P).weq (fun _ _ _ h ↦ h.1)))).toHomotopyEquiv.trans
    (splitRowDiagonalHomotopyEquiv P hcone)).trans
      (TopCat.homeoOfIso (SSet.toTop.mapIso
        (weakRowDiagonalIso (complexSubcategoryExact P) (complexSubcategory P).cof
          (complexSubcategory P).weq (fun _ _ _ h ↦ h)).symm)).toHomotopyEquiv

/-- The equivalence's forward map is exactly the original, canonical
change-of-cofibrations realization map. -/
@[simp]
theorem splitDeloopingHomotopyEquiv_toFun :
    (splitDeloopingHomotopyEquiv P hcone).toFun =
      (deloopingMap (splitComplexSubcategory_to_complexSubcategory_exact P)).hom := by
  change (SSet.toTop.map _).hom.comp
    ((SSet.toTop.map (TheoremA.diagonalMap (splitRowNerveInclusion P))).hom.comp
      (SSet.toTop.map _).hom) = _
  rw [← TopCat.hom_comp, ← TopCat.hom_comp, ← SSet.toTop.map_comp,
    ← SSet.toTop.map_comp]
  exact congrArg (fun f ↦ (SSet.toTop.map f).hom)
    (weakRowDiagonalIso_inclusion_reassembled (complexSubcategoryExact P)
      (splitComplexSubcategory P).cof (complexSubcategory P).weq
      (fun _ _ _ h ↦ h.1) (complexSubcategory P).cof (fun _ _ _ h ↦ h)
      (fun _ _ _ h ↦ h.1) (splitComplexSubcategory_to_complexSubcategory_exact P))

end Quillen.Waldhausen
