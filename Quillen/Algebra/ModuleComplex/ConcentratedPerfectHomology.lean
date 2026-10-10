/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Algebra.ModuleComplex.FiniteProjectiveHomology
import Quillen.Algebra.ModuleComplex.FiniteFreeAttachment
import Quillen.Algebra.ModuleComplex.PrincipalTailTruncation

/-!
# A finite-projective single model for the concentrated remainder

For a bounded finite-projective complex supported termwise in degrees at least
`n` and cohomologically at most `n`, the genuine upper-tail cycle splittings
make its original degree-`n` homology finite projective. Actual principal-local
derived models with the same lower term bound imply this globally by proved
finite-projective locality. Exact localization detects the original lower
cohomological bound, and projective lifting constructs an actual map from the
single complex on the original homology to the original complex, inducing its
identity and a quasi-isomorphism. The local lower *term* bound is essential;
cohomological concentration alone would not imply projectivity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Quillen.ModuleComplex
variable {R : Type u} [CommRing R]

/-- At the lower edge of a bounded finite-projective model, concentrated
cohomology is itself finite projective. The upper acyclic tail is split by
the actual cycle-sequence induction. -/
lemma finiteProjective_homology_of_bounded_model
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n b : ℤ) [K.IsLE n]
    (hbelow : ∀ i, i < n → IsZero (K.X i))
    (hbound : ∀ i, b < i → IsZero (K.X i))
    (hfinite : ∀ i, Module.Finite R (K.X i))
    (hprojective : ∀ i, Projective (K.X i)) :
    Module.Finite R (K.homology n) ∧ Projective (K.homology n) := by
  obtain ⟨hf, hp⟩ := finite_projective_cycles_above_cohomology_bound K n b
    hbound hfinite hprojective n le_rfl
  let e : K.cycles n ≅ K.homology n :=
    K.isoHomologyπ (n-1) n (by simp) ((hbelow (n-1) (by omega)).eq_of_src _ _)
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Projective.of_iso e hp⟩

local instance concentratedStandardDerived (S : Type u) [Ring S] : HasDerivedCategory.{u+1} (ModuleCat.{u} S) :=
  HasDerivedCategory.standard _

/-- A principal cover detects the original lower cohomological bound, through
actual local derived isomorphisms and exact localization. -/
lemma isGE_of_principal_derived_models
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (s : Set R) (hs : Ideal.span s = ⊤)
    (hlocal : ∀ r : s,
      ∃ P : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ,
        P.IsGE n ∧ Nonempty (DerivedCategory.Q.obj
          ((PrincipalLocalization.localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    K.IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  apply PrincipalLocalization.isZero_of_localizationSpan s hs
  intro r
  obtain ⟨P, hP, ⟨e⟩⟩ := hlocal r
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  let L : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ :=
    (PrincipalLocalization.localize r.val (.up ℤ)).obj K
  have : L.IsGE n := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm n
  have hz := (exactAt_iff_isZero_homology L i).mp (L.exactAt_of_isGE n i hi)
  exact hz.of_iso ((K.sc i).mapHomologyIso F).symm

/-- Actual principal-local finite-projective derived models with no terms below
`n` make the original top cohomology finite projective globally. -/
lemma finiteProjective_homology_of_principal_derived_models
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsLE n]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (hlocal : ∀ r : s,
      ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ) (b : ℤ),
        (∀ i, i < n → IsZero (P.X i)) ∧
        (∀ i, b < i → IsZero (P.X i)) ∧
        (∀ i, Module.Finite (Localization.Away r.val) (P.X i)) ∧
        (∀ i, Projective (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj
          ((PrincipalLocalization.localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    Module.Finite R (K.homology n) ∧ Module.Projective R (K.homology n) := by
  have hloc (r : s) :
      Module.Finite (Localization.Away r.val)
        ((K.homology n).localizedModule (Submonoid.powers r.val)) ∧
      Module.Projective (Localization.Away r.val)
        ((K.homology n).localizedModule (Submonoid.powers r.val)) := by
    obtain ⟨P, b, hbelow, hb, hfinite, hprojective, ⟨e⟩⟩ := hlocal r
    let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
    let L : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ :=
      (PrincipalLocalization.localize r.val (.up ℤ)).obj K
    have : L.IsLE n := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      exact (K.exactAt_of_isLE n i hi).map F
    have : P.IsLE n := by
      rw [← DerivedCategory.isLE_Q_obj_iff]
      exact DerivedCategory.TStructure.t.isLE_of_iso e n
    let eH : L.homology n ≅ P.homology n :=
      ((DerivedCategory.homologyFunctorFactors _ n).app L).symm ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app P
    let eF : L.homology n ≅ F.obj (K.homology n) := (K.sc n).mapHomologyIso F
    obtain ⟨hf, hp⟩ := finiteProjective_homology_of_bounded_model P n b hbelow hb hfinite hprojective
    have : Projective ((K.homology n).localizedModule (Submonoid.powers r.val)) :=
      Projective.of_iso (eH.symm ≪≫ eF) hp
    exact ⟨Module.Finite.equiv (eH.symm ≪≫ eF).toLinearEquiv,
      ModuleCat.projective_of_module_projective _⟩
  exact PrincipalLocalization.finiteProjective_of_localizationSpan s hs (K.homology n)
    (fun r => (hloc r).1) (fun r => (hloc r).2)

/-- The literal projective lift of the identity of the original homology is a
quasi-isomorphism when the original complex has cohomology only in that degree. -/
lemma quasiIso_fromSingleHomologyLift_id
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [K.IsLE n] [K.IsGE n] [Projective (K.homology n)] :
    QuasiIso (fromSingleHomologyLift K n (K.homology n) (𝟙 _)) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = n
  · subst i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have h := fromSingleHomologyLift_homology K n (K.homology n) (𝟙 _)
    have : IsIso ((singleObjHomologySelfIso (.up ℤ) n (K.homology n)).inv ≫
        homologyMap (fromSingleHomologyLift K n (K.homology n) (𝟙 _)) n) := by
      rw [h]
      infer_instance
    exact (isIso_comp_left_iff
      (singleObjHomologySelfIso (.up ℤ) n (K.homology n)).inv _).mp inferInstance
  · apply (quasiIsoAt_iff_exactAt _ i
      (exactAt_single_obj (.up ℤ) n (K.homology n) i hi)).mpr
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact K.exactAt_of_isGE n i hi
    · exact K.exactAt_of_isLE n i hi

/-- The concentrated remainder of a finite cone construction has an actual
finite-projective single-complex model over the original ring. Its comparison
map induces the original identity on homology, not merely an unspecified
isomorphism in a quotient category. -/
lemma exists_finiteProjective_single_of_principal_derived_models
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsLE n]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (hlocal : ∀ r : s,
      ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ) (b : ℤ),
        (∀ i, i < n → IsZero (P.X i)) ∧
        (∀ i, b < i → IsZero (P.X i)) ∧
        (∀ i, Module.Finite (Localization.Away r.val) (P.X i)) ∧
        (∀ i, Projective (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj
          ((PrincipalLocalization.localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    Module.Finite R (K.homology n) ∧ Module.Projective R (K.homology n) ∧
      ∃ f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj (K.homology n) ⟶ K,
        QuasiIso f ∧ (singleObjHomologySelfIso (.up ℤ) n (K.homology n)).inv ≫
          homologyMap f n = 𝟙 _ := by
  obtain ⟨hf, hp⟩ := finiteProjective_homology_of_principal_derived_models K n s hs hlocal
  have : Projective (K.homology n) := ModuleCat.projective_of_categoryTheory_projective _
  have : K.IsGE n := isGE_of_principal_derived_models K n s hs (fun r => by
    obtain ⟨P, b, hbelow, _, _, _, he⟩ := hlocal r
    have : P.IsStrictlyGE n := (CochainComplex.isStrictlyGE_iff P n).mpr hbelow
    exact ⟨P, inferInstance, he⟩)
  exact ⟨hf, hp, fromSingleHomologyLift K n (K.homology n) (𝟙 _),
    quasiIso_fromSingleHomologyLift_id K n,
    fromSingleHomologyLift_homology K n (K.homology n) (𝟙 _)⟩

end Quillen.ModuleComplex
