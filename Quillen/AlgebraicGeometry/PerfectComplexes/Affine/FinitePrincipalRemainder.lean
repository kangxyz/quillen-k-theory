/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.HomologyCover
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalApproximation

/-! # The actual vector-bundle remainder on a finite union of principal opens

The actual principal-local finite-projective homology identifies the homology
sheaf on the covered open as finite locally free. Cohomological concentration
then gives its original derived single model. Neither global projectivity of
the ambient module nor splitting of the approximation triangle is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
open Quillen.ModuleComplex.PrincipalLocalization

/-- Restriction to a displayed principal chart is the actual associated localized complex. -/
def principalChartAssociatedComplexIso (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (r : R)
    (k : Spec (.of (Localization.Away r)) ⟶ U) [IsOpenImmersion k]
    (hk : k ≫ j = CoherentScheme.principalOpen R r) (C : ModuleComplex R) :
    (restrict k).obj ((restrict j).obj ((associatedComplex R).obj C)) ≅
      (associatedComplex (.of (Localization.Away r))).obj ((localize r (.up ℤ)).obj C) :=
  (restrictCompIso k j).app ((associatedComplex R).obj C) ≪≫
    (eqToIso (restrict_congr hk)).app ((associatedComplex R).obj C) ≪≫
    ((principalRestrictionAssociatedComplexIso R r).app C).symm

/-- Original localized finite-projective residual homology yields a vector bundle
on the actually covered open, and a derived single on that same homology sheaf. -/
theorem vectorBundle_single_of_principal_concentration
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (C : ModuleComplex R) (a : ℤ) (s : Finset R)
    (k : ∀ r : s, Spec (.of (Localization.Away r.val)) ⟶ U)
    [∀ r : s, IsOpenImmersion (k r)]
    (hk : ∀ r : s, k r ≫ j = CoherentScheme.principalOpen R r.val)
    (hcover : ∀ x : U, ∃ r : s, ∃ y, k r y = x)
    (hlocal : ∀ r : s,
      let L : ModuleComplex (.of (Localization.Away r.val)) := (localize r.val (.up ℤ)).obj C
      L.IsLE a ∧ L.IsGE a ∧ Module.Finite (Localization.Away r.val) (L.homology a) ∧
        Projective (L.homology a)) :
    let D := (restrict j).obj ((associatedComplex R).obj C)
    SchemeSheaf.IsFiniteLocallyFree U (D.homology a) ∧ D.IsGE a ∧ D.IsLE a ∧
      Nonempty ((toDerived U).obj D ≅ (toDerived U).obj
        ((CochainComplex.singleFunctor U.Modules a).obj (D.homology a))) := by
  let D := (restrict j).obj ((associatedComplex R).obj C)
  let Y (r : s) := Spec (.of (Localization.Away r.val))
  have hmodels (r : s) : ((restrict (k r)).obj D).IsLE a ∧
      ((restrict (k r)).obj D).IsGE a ∧
      SchemeSheaf.IsFiniteLocallyFree (Y r) (((restrict (k r)).obj D).homology a) := by
    let L : ModuleComplex (.of (Localization.Away r.val)) := (localize r.val (.up ℤ)).obj C
    obtain ⟨hhi, hlo, hfin, hproj⟩ := hlocal r
    let F := tilde.functor (.of (Localization.Away r.val))
    let : F.Additive := AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor
    let : F.PreservesHomology := CoherentScheme.tilde_preservesHomology _
    let E := (associatedComplex (.of (Localization.Away r.val))).obj L
    have hEhi : E.IsLE a := by
      rw [CochainComplex.isLE_iff]
      intro n hn
      exact (L.exactAt_of_isLE a n hn).map F
    have hElo : E.IsGE a := by
      rw [CochainComplex.isGE_iff]
      intro n hn
      exact (L.exactAt_of_isGE a n hn).map F
    let e := principalChartAssociatedComplexIso R j r.val (k r) (hk r) C
    have hle := CochainComplex.isLE_of_iso e.symm a
    have hge := CochainComplex.isGE_of_iso e.symm a
    let eH : (((restrict (k r)).obj D).homology a) ≅ F.obj (L.homology a) :=
      (HomologicalComplex.homologyFunctor _ _ a).mapIso e ≪≫ (L.sc a).mapHomologyIso F
    have : Module.Projective (Localization.Away r.val) (L.homology a) :=
      ModuleCat.projective_of_module_projective _
    have : SchemeSheaf.IsFiniteLocallyFree (Y r) (F.obj (L.homology a)) :=
      SchemeSheaf.finiteLocallyFree_tilde_of_finite_projective (.of (Localization.Away r.val)) _
    exact ⟨hle, hge, SchemeSheaf.finiteLocallyFree_of_iso eH.symm⟩
  have hge := isGE_of_openImmersionCover D Y k hcover a (fun r => (hmodels r).2.1)
  have hle := isLE_of_openImmersionCover D Y k hcover a (fun r => (hmodels r).1)
  obtain ⟨hvb, he⟩ := exists_vectorBundle_single_of_openImmersionCover D Y k hcover a
    (fun r => (hmodels r).2.1) (fun r => (hmodels r).1) (fun r => (hmodels r).2.2)
  exact ⟨hvb, hge, hle, he⟩

/-- The proved finite-principal approximation has an actual vector-bundle
remainder on the covered open. Its global source and map are unchanged, and
its residual single is formed from the original restricted cone homology. -/
theorem exists_moduleStrictPerfect_approximation_with_vectorBundle_remainder
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (K : ModuleComplex R) (a b : ℤ) (s : Finset R)
    (k : ∀ r : s, Spec (.of (Localization.Away r.val)) ⟶ U)
    [∀ r : s, IsOpenImmersion (k r)]
    (hk : ∀ r : s, k r ≫ j = CoherentScheme.principalOpen R r.val)
    (hcover : ∀ x : U, ∃ r : s, ∃ y, k r y = x)
    (hbound : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) b)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      let D := (restrict j).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
      SchemeSheaf.IsFiniteLocallyFree U (D.homology a) ∧ D.IsGE a ∧ D.IsLE a ∧
        Nonempty ((toDerived U).obj D ≅ (toDerived U).obj
          ((CochainComplex.singleFunctor U.Modules a).obj (D.homology a))) := by
  obtain ⟨P, hP, f, hf⟩ :=
    exists_moduleStrictPerfect_approximation_with_local_projective_remainder R K a b s hbound hlocal
  exact ⟨P, hP, f, vectorBundle_single_of_principal_concentration R j
    (CochainComplex.mappingCone f) a s k hk hcover (fun r =>
      ⟨(hf r).1, (hf r).2.1, (hf r).2.2.1, (hf r).2.2.2.1⟩)⟩

end Quillen.PerfectComplexes.Affine
