/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.DerivedPreEqualityDenominators

/-! # One genuine pre-quasi-isomorphism for finitely many actual chain homotopies -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w t
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

lemma exists_pre_quasiIso_finite_homotopies_of_derived_eq
    {K : CochainComplex C ℤ} {ι : Type t} (s : Finset ι)
    (L : ι → CochainComplex C ℤ) (f g : ∀ i, K ⟶ L i)
    (h : ∀ i ∈ s, DerivedCategory.Q.map (f i) = DerivedCategory.Q.map (g i)) :
    ∃ (M : CochainComplex C ℤ) (q : M ⟶ K), QuasiIso q ∧
      ∀ i ∈ s, Nonempty (Homotopy (q ≫ f i) (q ≫ g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨K,𝟙 K,inferInstance,by simp⟩
  | @insert i s hi ih =>
      obtain ⟨M,q,hq,Hq⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
      have he : DerivedCategory.Q.map (q ≫ f i) = DerivedCategory.Q.map (q ≫ g i) := by
        simp only [Functor.map_comp,h i (Finset.mem_insert_self i s)]
      obtain ⟨N,r,hr,⟨Hr⟩⟩ := exists_pre_quasiIso_homotopy_of_derived_eq _ _ he
      refine ⟨N,r ≫ q,inferInstance,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact ⟨by simpa only [Category.assoc] using Hr⟩
      · obtain ⟨H⟩ := Hq k hk
        exact ⟨by simpa only [Category.assoc] using H.compLeft r⟩

end Quillen.CochainComplex
