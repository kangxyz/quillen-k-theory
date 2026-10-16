/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedRoofs
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-! # Common actual supported roofs for finite families of local derived arrows -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- A finite family of original local derived arrows has a single actual
global source-supported denominator and actual numerators to every original target. -/
lemma exists_source_supported_finite_roof {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) {ι : Type v} (s : Finset ι)
    (B : ι → CochainComplex X.Modules ℤ) (hB : ∀ i, locallyPerfect X (B i))
    (hzA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (φ : ∀ i, (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj (B i))) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (g : ∀ i ∈ s, M ⟶ B i), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj
        ((restrict T.ι).obj M)) ∧
      ∀ i (hi : i ∈ s), (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ φ i =
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map (g i hi)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨A,𝟙 A,(fun i hi => False.elim (Finset.notMem_empty i hi)),hA,?_,hzA,?_⟩
      · rw [CategoryTheory.Functor.map_id]
        infer_instance
      · simp
  | @insert i s hi ih =>
      obtain ⟨M,q,g,hM,hq,hzM,hg⟩ := ih
      obtain ⟨N,r,a,hN,hr,ha,hzN⟩ := exists_source_supported_derived_roof j T hT hM (hB i) hzM
        ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ φ i)
      let g' : ∀ k ∈ insert i s, N ⟶ B k := fun k hk => by
        by_cases e : k = i
        · subst k; exact a
        · exact r ≫ g k ((Finset.mem_insert.mp hk).resolve_left e)
      refine ⟨N,r ≫ q,g',hN,?_,hzN,?_⟩
      · rw [Functor.map_comp]
        infer_instance
      · intro k hk
        by_cases e : k = i
        · subst k
          simpa only [g',dite_eq_left rfl,Functor.map_comp,Category.assoc] using ha
        · have hks := (Finset.mem_insert.mp hk).resolve_left e
          dsimp [g']
          rw [dite_eq_right e,Functor.map_comp,Functor.map_comp,Category.assoc,hg k hks,
            Functor.map_comp,Functor.map_comp]

end Quillen.PerfectComplexes.OpenDerivedImage
