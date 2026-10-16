/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ModulePerfectClosure
public import Quillen.Algebra.ModuleComplex.FiniteProjectiveHomology
public import Quillen.Algebra.ModuleComplex.FiniteFreeAttachment
public import Quillen.Algebra.ModuleComplex.ConcentratedPerfectHomology
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-!
# Finite-principal descent of perfect module models

Actual finite-free highest-homology attachments lower the cohomological
upper bound while preserving the common lower term bound of genuine
principal-local finite-projective models. Finite induction ends in a
concentrated finite-projective single complex, and original distinguished
triangles reconstruct a global bounded finite-projective model. This works
over arbitrary rings and includes empty covers of the zero ring.

The finite attachment argument follows the local pseudo-coherence method
of Stacks Project, Tag 066D, without an infinite-resolution premise.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex TopologicalSpace

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard

/-- Replacing the target in the actual derived category preserves a specified lower term bound of
  the cone. -/
lemma exists_moduleStrictPerfect_cone_model_boundedBelow (R : CommRingCat.{u})
    {P K L : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hL : moduleStrictPerfect R L) (f : P ⟶ K) (a : ℤ)
    (hPb : ∀ i, i < a + 1 → IsZero (P.X i))
    (hLb : ∀ i, i < a → IsZero (L.X i))
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ (C : ModuleComplex R), moduleStrictPerfect R C ∧
      (∀ i, i < a → IsZero (C.X i)) ∧
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone f) ≅ DerivedCategory.Q.obj C) :=
        by
  have := isKProjective_of_moduleStrictPerfect R hP
  obtain ⟨g, hg⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective
    (DerivedCategory.Q.map f ≫ e.hom)
  refine ⟨CochainComplex.mappingCone g, moduleStrictPerfect_mappingCone R hP hL g,
    fun i hi => ?_, ⟨?_⟩⟩
  · exact (CochainComplex.mappingCone.isZero_X_iff g i).mpr
      ⟨hPb (i+1) (by omega), hLb i hi⟩
  · exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _
      (DerivedCategory.mappingCone_triangle_distinguished f)
      (DerivedCategory.mappingCone_triangle_distinguished g) (Iso.refl _) e (by simpa using
        hg.symm))

/-- An attachment strictly above the common lower term bound preserves that bound in every original
  principal-local model. -/
lemma principal_perfect_models_mappingCone_single (R : CommRingCat.{u})
    (K : ModuleComplex R) (a n : ℤ) (han : a < n) (s : Finset R)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P))
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M]
    (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj M ⟶ K) :
    ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj
        (CochainComplex.mappingCone f)) ≅ DerivedCategory.Q.obj P) := by
  intro r
  obtain ⟨L, hL, hLb, ⟨e⟩⟩ := hlocal r
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  have hP := moduleStrictPerfect_localize R r.val (moduleStrictPerfect_single R n M)
  obtain ⟨C, hC, hCb, ⟨eC⟩⟩ := exists_moduleStrictPerfect_cone_model_boundedBelow
    (CommRingCat.of (Localization.Away r.val)) hP hL ((localize r.val (.up ℤ)).map f) a
    (fun i hi => F.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) n M i (by omega)))
    hLb e
  exact ⟨C, hC, hCb, ⟨DerivedCategory.Q.mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f F) ≪≫ eC⟩⟩

/-- Actual finite principal models supply a finite-free top attachment whose original cone lowers
  the upper bound and retains the local lower bound. -/
lemma exists_finiteFree_single_lowering_principal_models (R : CommRingCat.{u})
    (K : ModuleComplex R) (a n : ℤ) [K.IsLE n] (han : a < n)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K),
      Epi (HomologicalComplex.homologyMap f n) ∧ (CochainComplex.mappingCone f).IsLE (n-1) ∧
      ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
        moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
        (∀ i, i < a → IsZero (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj
          (CochainComplex.mappingCone f)) ≅ DerivedCategory.Q.obj P) := by
  have : Module.Finite R (K.homology n) :=
    Quillen.ModuleComplex.finite_top_homology_of_principal_perfect_models K n s hs (fun r => by
      obtain ⟨P, ⟨⟨c, b, hb⟩, hp⟩, _, e⟩ := hlocal r
      refine ⟨P, b, fun i hi => hb i (Or.inr hi), fun i => (hp i).1, fun i => ?_, e⟩
      let := (hp i).2
      infer_instance)
  obtain ⟨m, f, hf, hcone⟩ := Quillen.ModuleComplex.exists_finiteFree_single_lowering_top K n
  exact ⟨m, f, hf, hcone, principal_perfect_models_mappingCone_single R K a n han s hlocal _ f⟩

end Quillen.PerfectComplexes.Affine

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard

/-- The concentrated remainder has the original finite-projective homology as a genuine
  single-complex model. -/
lemma finiteProjectiveDerived_of_principal_models_base (R : CommRingCat.{u})
    (K : ModuleComplex R) (a : ℤ) [K.IsLE a]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    finiteProjectiveDerivedObjects R (DerivedCategory.Q.obj K) := by
  obtain ⟨hf, hp, f, hq, _⟩ :=
    Quillen.ModuleComplex.exists_finiteProjective_single_of_principal_derived_models
      K a (s : Set R) hs (fun r => by
        obtain ⟨P, ⟨⟨c, b, hb⟩, hterms⟩, hbelow, e⟩ := hlocal r
        refine ⟨P, b, hbelow, fun i hi => hb i (Or.inr hi), fun i => (hterms i).1, fun i => ?_, e⟩
        let := (hterms i).2
        infer_instance)
  exact ⟨_, moduleStrictPerfect_single R a (K.homology a), ⟨asIso (DerivedCategory.Q.map f)⟩⟩

/-- Finite cone induction descends genuine principal-local perfect models to a global bounded
  finite-projective derived representative. -/
lemma finiteProjectiveDerived_of_principal_models (R : CommRingCat.{u})
    (K : ModuleComplex R) (a b : ℤ) [K.IsLE b]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    finiteProjectiveDerivedObjects R (DerivedCategory.Q.obj K) := by
  by_cases hab : a ≤ b
  · induction b, hab using Int.leInduction generalizing K with
    | base => exact finiteProjectiveDerived_of_principal_models_base R K a s hs hlocal
    | succ n hn ih =>
      obtain ⟨m, f, _, hcone, hmodels⟩ :=
        exists_finiteFree_single_lowering_principal_models R K a (n+1) (by omega) s hs hlocal
      have : (CochainComplex.mappingCone f).IsLE n := by simpa using hcone
      have hC := ih (CochainComplex.mappingCone f) hmodels
      exact (finiteProjectiveDerivedObjects R).ext_of_isTriangulatedClosed₂ _
        (DerivedCategory.mappingCone_triangle_distinguished f)
        ⟨_, moduleStrictPerfect_single R (n+1) (ModuleCat.of R (Fin m → R)), ⟨Iso.refl _⟩⟩ hC
  · have : K.IsLE a := K.isLE_of_le b a (by omega)
    exact finiteProjectiveDerived_of_principal_models_base R K a s hs hlocal

end Quillen.PerfectComplexes.Affine
