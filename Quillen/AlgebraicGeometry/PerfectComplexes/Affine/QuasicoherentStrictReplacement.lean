/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.Strictification

/-!
# Actual affine strict replacements for termwise quasicoherent complexes

The proved finite-projective module strictification and genuine K-projective
chain representatives produce an actual strict-perfect quasi-isomorphism to
any affine locally-perfect complex with quasicoherent terms. The construction
uses literal global sections and the original affine reconstruction counit.
The original module-derived isomorphism and the geometric associated-derived
comparison formula are retained. Terms of the target may be unbounded.

Termwise quasicoherence is explicit and essential for this chain-level
endpoint; the preceding derived strictification applies more generally to all
ambient sheaf complexes but does not assert an actual chain map to them.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- A termwise quasicoherent affine locally-perfect complex admits an actual
finite-projective module chain replacement of its literal global sections.
The source is made K-projective by its proved bounded projective terms. -/
lemma locallyPerfect_sections_exists_moduleStrictPerfect_derivedIso_lift (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : ModuleComplex R), moduleStrictPerfect R P ∧
      ∃ (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj ((sectionsComplex R).obj K))
        (f : P ⟶ (sectionsComplex R).obj K), DerivedCategory.Q.map f = e.hom ∧ QuasiIso f := by
  let L := (sectionsComplex R).obj K
  let e := associatedSectionsIsoOfQuasicoherent R K hqc
  have hL : locallyPerfect (Spec R) ((associatedComplex R).obj L) :=
    (locallyPerfect_iff_of_derivedIso ((toDerived (Spec R)).mapIso e)).mpr hK
  obtain ⟨a, b, hab⟩ := locallyPerfect_homology_bounded hL
  have : L.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    apply Functor.reflects_exact_of_faithful (tilde.functor R) (L.sc i)
    exact (exactAt_iff_isZero_homology _ i).mpr (hab i (Or.inl hi))
  have : L.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    apply Functor.reflects_exact_of_faithful (tilde.functor R) (L.sc i)
    exact (exactAt_iff_isZero_homology _ i).mpr (hab i (Or.inr hi))
  obtain ⟨P, hP, ⟨eP⟩⟩ := finiteProjectiveDerived_of_locallyPerfect_associated R L a b hL
  have : P.IsKProjective := isKProjective_of_moduleStrictPerfect R hP
  obtain ⟨f, hf⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective eP.hom
  have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
  exact ⟨P, hP, eP, f, hf, (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mp inferInstance⟩

/-- The actual module chain replacement, retaining literal global sections. -/
lemma locallyPerfect_sections_exists_moduleStrictPerfect_quasiIso (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : ModuleComplex R), moduleStrictPerfect R P ∧
      ∃ f : P ⟶ (sectionsComplex R).obj K, QuasiIso f := by
  obtain ⟨P, hP, _, f, _, hf⟩ := locallyPerfect_sections_exists_moduleStrictPerfect_derivedIso_lift
    R hK hqc
  exact ⟨P, hP, f, hf⟩

/-- The geometric chain map through the original affine counit realizes the
literal associated-derived image of its original module chain map. -/
lemma associated_counit_comparison_derived_map (R : CommRingCat.{u})
    {P : ModuleComplex R} {K : Complex (Spec R)}
    (hqc : ∀ i, (K.X i).IsQuasicoherent)
    (f : P ⟶ (sectionsComplex R).obj K) :
    (toDerived (Spec R)).map ((associatedComplex R).map f ≫
      (associatedSectionsIsoOfQuasicoherent R K hqc).hom) =
      ((associatedDerivedFactors R).app P).inv ≫
        (associatedDerived R).map (DerivedCategory.Q.map f) ≫
        ((associatedDerivedFactors R).app ((sectionsComplex R).obj K)).hom ≫
        (toDerived (Spec R)).map (associatedSectionsIsoOfQuasicoherent R K hqc).hom := by
  rw [Functor.map_comp, ← cancel_epi ((associatedDerivedFactors R).app P).hom]
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Functor.comp_map, Category.assoc, Iso.app_hom] using (congrArg (fun t => t ≫
    (toDerived (Spec R)).map (associatedSectionsIsoOfQuasicoherent R K hqc).hom)
      ((associatedDerivedFactors R).hom.naturality f)).symm

/-- The actual associated replacement followed by the original sheafification
counit is a quasi-isomorphism to the original termwise-QC target. -/
lemma locallyPerfect_exists_associated_quasiIso_of_quasicoherent (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : ModuleComplex R), moduleStrictPerfect R P ∧
      ∃ f : P ⟶ (sectionsComplex R).obj K,
        QuasiIso f ∧ QuasiIso ((associatedComplex R).map f ≫
          (associatedSectionsIsoOfQuasicoherent R K hqc).hom) := by
  obtain ⟨P, hP, f, hf⟩ := locallyPerfect_sections_exists_moduleStrictPerfect_quasiIso R hK hqc
  have : QuasiIso ((associatedComplex R).map f) := (quasiIso_associated_iff R f).mpr hf
  exact ⟨P, hP, f, hf, inferInstance⟩

/-- Every termwise quasicoherent affine locally-perfect complex has an actual
strict-perfect chain complex mapping quasi-isomorphically to it. Termwise QC
is essential for the actual chain endpoint, unlike the derived representative
statement for arbitrary ambient sheaf complexes. -/
lemma locallyPerfect_exists_strictPerfect_quasiIso_of_quasicoherent (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : StrictPerfect (Spec R)) (f : P.obj ⟶ K), QuasiIso f := by
  obtain ⟨P, hP, f, _, hf⟩ := locallyPerfect_exists_associated_quasiIso_of_quasicoherent R hK hqc
  exact ⟨⟨(associatedComplex R).obj P, strictPerfect_associated R hP⟩,
    (associatedComplex R).map f ≫ (associatedSectionsIsoOfQuasicoherent R K hqc).hom, hf⟩

end Quillen.PerfectComplexes.Affine
