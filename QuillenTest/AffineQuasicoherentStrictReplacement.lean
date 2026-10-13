/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.QuasicoherentStrictReplacement

/-! Semantic consumers of original affine termwise-QC strict chain replacements. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
attribute [local instance] Quillen.PerfectComplexes.Affine.standardDerivedModules
  Quillen.PerfectComplexes.Affine.standardDerivedSheaves
namespace QuillenTest.AffineQuasicoherentStrictReplacement

open Quillen

/-- The geometric comparison literally uses the original affine counit in
 every degree, with no replacement of its target by a quasi-isomorphic object. -/
theorem actual_component_counit (R : CommRingCat.{u})
    {P : ModuleComplex R} {K : Complex (Spec R)}
    (hqc : ∀ i, (K.X i).IsQuasicoherent) (f : P ⟶ (sectionsComplex R).obj K) (i : ℤ) :
    ((associatedComplex R).map f ≫ (associatedSectionsIsoOfQuasicoherent R K hqc).hom).f i =
      (tilde.functor R).map (f.f i) ≫ (K.X i).fromTildeΓ := rfl

/-- The original strict source maps into the original unbounded termwise-QC
 target and induces isomorphisms on all its actual homology sheaves. -/
theorem actual_strict_map_all_homology (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : StrictPerfect (Spec R)) (f : P.obj ⟶ K),
      ∀ i, IsIso (homologyMap f i) := by
  obtain ⟨P, f, hf⟩ := locallyPerfect_exists_strictPerfect_quasiIso_of_quasicoherent R hK hqc
  exact ⟨P, f, fun _ => inferInstance⟩

/-- Both directions of the originally selected module-derived isomorphism
 remain the inverse of the actual chain representative. -/
theorem actual_module_derived_inverse (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : ModuleComplex R), moduleStrictPerfect R P ∧
      ∃ (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj ((sectionsComplex R).obj K))
        (f : P ⟶ (sectionsComplex R).obj K), QuasiIso f ∧
          DerivedCategory.Q.map f = e.hom ∧
          DerivedCategory.Q.map f ≫ e.inv = 𝟙 _ ∧ e.inv ≫ DerivedCategory.Q.map f = 𝟙 _ := by
  obtain ⟨P, hP, e, f, he, hf⟩ :=
    locallyPerfect_sections_exists_moduleStrictPerfect_derivedIso_lift R hK hqc
  refine ⟨P, hP, e, f, hf, he, ?_, ?_⟩ <;> simp only [he, Iso.hom_inv_id, Iso.inv_hom_id]

/-- The actual sheaf map agrees with the original derived comparison of the
 chosen module model, including the literal reconstruction counit. -/
theorem actual_geometric_derived_formula (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K)
    (hqc : ∀ i, (K.X i).IsQuasicoherent) :
    ∃ (P : ModuleComplex R), moduleStrictPerfect R P ∧
      ∃ (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj ((sectionsComplex R).obj K))
        (f : P ⟶ (sectionsComplex R).obj K), QuasiIso f ∧
        (toDerived (Spec R)).map ((associatedComplex R).map f ≫
          (associatedSectionsIsoOfQuasicoherent R K hqc).hom) =
          ((associatedDerivedFactors R).app P).inv ≫
            (associatedDerived R).map e.hom ≫
            ((associatedDerivedFactors R).app ((sectionsComplex R).obj K)).hom ≫
            (toDerived (Spec R)).map (associatedSectionsIsoOfQuasicoherent R K hqc).hom := by
  obtain ⟨P, hP, e, f, he, hf⟩ :=
    locallyPerfect_sections_exists_moduleStrictPerfect_derivedIso_lift R hK hqc
  refine ⟨P, hP, e, f, hf, ?_⟩
  rw [associated_counit_comparison_derived_map, he]

end QuillenTest.AffineQuasicoherentStrictReplacement
