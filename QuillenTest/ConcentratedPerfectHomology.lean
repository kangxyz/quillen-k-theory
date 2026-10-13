/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.ModuleComplex.ConcentratedPerfectHomology
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedComparison

/-! Semantic consumers of the actual finite-projective concentrated remainder. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
namespace QuillenTest.ConcentratedPerfectHomology

open Quillen

/-- The actual lift sends the original homology to itself by the identity and
is an isomorphism on every original homology object. -/
theorem actual_single_lift_all_homology {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [K.IsLE n] [K.IsGE n] [Projective (K.homology n)] :
    (∀ i, IsIso (homologyMap (fromSingleHomologyLift K n (K.homology n) (𝟙 _)) i)) ∧
      (singleObjHomologySelfIso (.up ℤ) n (K.homology n)).inv ≫
        homologyMap (fromSingleHomologyLift K n (K.homology n) (𝟙 _)) n = 𝟙 _ := by
  have := quasiIso_fromSingleHomologyLift_id K n
  exact ⟨fun _ => inferInstance, fromSingleHomologyLift_homology K n (K.homology n) (𝟙 _)⟩

/-- The actual geometric associated-sheaf lift is a quasi-isomorphism in the
original category of all sheaf complexes. -/
theorem actual_associated_single_lift (R : CommRingCat.{u}) (K : ModuleComplex R) (n : ℤ)
    [K.IsLE n] [K.IsGE n] [Projective (K.homology n)] :
    QuasiIso ((associatedComplex R).map (fromSingleHomologyLift K n (K.homology n) (𝟙 _))) :=
  (quasiIso_associated_iff R _).mpr (quasiIso_fromSingleHomologyLift_id K n)

section LocalModels
variable {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsLE n]
    (s : Set R) (hs : Ideal.span s = ⊤)
    (hlocal : ∀ r : s,
      ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ) (b : ℤ),
        (∀ i, i < n → IsZero (P.X i)) ∧
        (∀ i, b < i → IsZero (P.X i)) ∧
        (∀ i, Module.Finite (Localization.Away r.val) (P.X i)) ∧
        (∀ i, Projective (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj
          ((PrincipalLocalization.localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P))

include hs hlocal in
/-- Local perfection at the lower edge supplies actual lifts from the original
homology against arbitrary original module epimorphisms. -/
theorem actual_global_homology_lift {A B : ModuleCat.{u} R} (p : A ⟶ B) [Epi p]
    (g : K.homology n ⟶ B) : ∃ l : K.homology n ⟶ A, l ≫ p = g := by
  let := (finiteProjective_homology_of_principal_derived_models K n s hs hlocal).2
  have : Projective (K.homology n) := ModuleCat.projective_of_categoryTheory_projective _
  exact ⟨Projective.factorThru g p, Projective.factorThru_comp g p⟩

include hs hlocal in
/-- The final model is literally the original homology module in the requested
single degree; the original chain map becomes invertible in the actual module
derived category. No global termwise projectivity of K is supplied. -/
theorem actual_single_derived_model :
    Module.Finite R (K.homology n) ∧ Module.Projective R (K.homology n) ∧
      ∃ f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj (K.homology n) ⟶ K,
        IsIso (DerivedCategory.Q.map f) ∧
        (singleObjHomologySelfIso (.up ℤ) n (K.homology n)).inv ≫ homologyMap f n = 𝟙 _ := by
  obtain ⟨hf, hp, f, hq, he⟩ :=
    exists_finiteProjective_single_of_principal_derived_models K n s hs hlocal
  exact ⟨hf, hp, f, inferInstance, he⟩
end LocalModels

/-- The actual empty principal cover of a zero ring remains valid. -/
theorem actual_zero_ring_empty_cover {R : Type u} [CommRing R] [Subsingleton R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsLE n] :
    ∃ f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj (K.homology n) ⟶ K,
      QuasiIso f := by
  obtain ⟨_, _, f, hq, _⟩ := exists_finiteProjective_single_of_principal_derived_models
    K n (∅ : Set R) (Subsingleton.elim _ _)
      (fun r => (Set.notMem_empty r.val r.property).elim)
  exact ⟨f, hq⟩

end QuillenTest.ConcentratedPerfectHomology
