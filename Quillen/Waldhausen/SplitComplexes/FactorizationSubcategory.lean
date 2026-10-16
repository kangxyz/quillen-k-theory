/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Subcategory
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationQuotient

/-!
# Split-cofibration factorizations inside cone-closed subcategories

Actual closure under mapping cones, together with the previously required
extension closure, keeps both the factorization object and its explicitly
identified quotient in the chosen full subcategory. This proves the
factorization property there; no approximation or K-equivalence theorem is
an assumption or a conclusion.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Waldhausen.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

include hcone

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts] in
/-- Every map in the full subcategory factors as an actual split cofibration
followed by an actual quasi-isomorphism in the same category. Its cofibration
quotient is the mapping cone of the negative original map. -/
theorem exists_subcategory_factorization {K L : P.FullSubcategory} (f : K ⟶ L) :
    ∃ (M : P.FullSubcategory) (i : K ⟶ M) (p : M ⟶ L),
      (splitComplexSubcategory P).cof i ∧ (splitComplexSubcategory P).weq p ∧ i ≫ p = f := by
  let M : P.FullSubcategory := ⟨middle f.hom, middle_property P hcone K.property L.property f.hom⟩
  let i : K ⟶ M := P.homMk (inclusion f.hom)
  let p : M ⟶ L := P.homMk (projection f.hom)
  refine ⟨M, i, p, ?_, ?_, ?_⟩
  · apply (splitSubcategoryCofibrations_iff P i).2
    exact ⟨mappingCone (-f.hom), hcone K.property L.property (-f.hom),
      quotientMap f.hom, inclusion_quotientMap f.hom,
      fun n ↦ ⟨quotientSequenceSplitting f.hom n⟩⟩
  · change QuasiIso (projection f.hom)
    infer_instance
  · exact ObjectProperty.hom_ext _ (inclusion_projection f.hom)

end Quillen.Waldhausen.SplitFactorization
