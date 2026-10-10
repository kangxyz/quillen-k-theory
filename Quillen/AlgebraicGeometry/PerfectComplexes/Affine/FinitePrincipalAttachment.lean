/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.AffineApproximation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectDescent

/-!
# Actual finite-free attachments on finite principal families

Finitely generated homology on finitely many principal opens admits one
actual global finite-free single-complex attachment. Its original localized
homology maps are epimorphisms, and its literal mapping cone lowers each
local upper cohomological bound. Genuine local finite-projective derived
models supply the required finite generation and retain their common lower
term bound after attachments strictly above that bound.

The finite family need not generate the unit ideal. Thus these results apply
to a quasi-compact open of an affine scheme even when it is a proper open.
No global finite generation, noetherianity, or ambient-sheaf projectivity is
assumed. The existing finite-submodule approximation is reused.

This is the finite-cover attachment step in Stacks Project, Tag 08EC.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex AlgebraicGeometry

namespace Quillen.ModuleComplex
variable {R : Type u} [CommRing R]

/-- An actual finite-free map is epic after localization on every member of
an arbitrary finite principal family. No unit-ideal cover assumption is used.
The existing finite-submodule approximation supplies the common finite source. -/
lemma exists_finiteFree_epi_on_principals (M : ModuleCat.{u} R) (s : Finset R)
    (hfinite : ∀ r : s, Module.Finite (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val))) :
    ∃ (m : ℕ) (g : ModuleCat.of R (Fin m → R) ⟶ M),
      ∀ r : s, Epi ((ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)).map g) := by
  let := hfinite
  obtain ⟨N, hN, htop⟩ := Quillen.CoherentScheme.exists_fg_submodule_localized_eq_top_finite
    (fun r : s => Submonoid.powers r.val) (fun r => Localization.Away r.val)
    (fun r => M.localizedModule (Submonoid.powers r.val))
    (fun r => M.localizedModuleMkLinearMap (Submonoid.powers r.val))
  let N' := ModuleCat.of R N
  let i : N' ⟶ M := ModuleCat.ofHom N.subtype
  have : Module.Finite R N := Module.Finite.of_fg hN
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R N
  let q' : ModuleCat.of R (Fin m → R) ⟶ N' := ModuleCat.ofHom q
  have : Epi q' := (ModuleCat.epi_iff_surjective q').mpr hq
  refine ⟨m, q' ≫ i, fun r => ?_⟩
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  have : IsIso (F.map i) :=
    Quillen.CoherentScheme.isIso_localized_subtype_of_eq_top
      (CommRingCat.of R) (Submonoid.powers r.val) M N (htop r)
  change Epi (F.map (q' ≫ i))
  rw [F.map_comp]
  infer_instance

end Quillen.ModuleComplex

namespace Quillen.ModuleComplex
open PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Finite homology after finitely many principal localizations admits a
single actual finite-free attachment, epic on the original localized homology. -/
lemma exists_finiteFree_single_epi_homology_on_principals
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (s : Finset R)
    (hfinite : ∀ r : s, Module.Finite (Localization.Away r.val)
      (((localize r.val (.up ℤ)).obj K).homology n)) :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K),
      ∀ r : s, Epi (homologyMap ((localize r.val (.up ℤ)).map f) n) := by
  have hfinite' (r : s) : Module.Finite (Localization.Away r.val)
      ((K.homology n).localizedModule (Submonoid.powers r.val)) := by
    let L : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ :=
      (localize r.val (.up ℤ)).obj K
    let e : L.homology n ≅ (K.homology n).localizedModule (Submonoid.powers r.val) :=
      (K.sc n).mapHomologyIso (ModuleCat.localizedModuleFunctor (Submonoid.powers r.val))
    have : Module.Finite (Localization.Away r.val) (L.homology n) := hfinite r
    exact Module.Finite.equiv e.toLinearEquiv
  obtain ⟨m, g, hg⟩ := exists_finiteFree_epi_on_principals (K.homology n) s hfinite'
  let P := ModuleCat.of R (Fin m → R)
  let A := (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj P
  let f := fromSingleHomologyLift K n P g
  refine ⟨m, f, fun r => ?_⟩
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  have : Epi (F.map g) := hg r
  have : Epi (F.map (homologyMap f n)) := by
    have he : F.map ((singleObjHomologySelfIso (.up ℤ) n P).inv) ≫
        F.map (homologyMap f n) = F.map g := by
      rw [← F.map_comp]
      exact congrArg F.map (fromSingleHomologyLift_homology K n P g)
    exact epi_of_epi_fac he
  have he : homologyMap ((localize r.val (.up ℤ)).map f) n ≫
      ((K.sc n).mapHomologyIso F).hom =
      ((A.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap f n) := by
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ (.up ℤ) n).map f) F
  have : Epi (homologyMap ((localize r.val (.up ℤ)).map f) n ≫
      ((K.sc n).mapHomologyIso F).hom) := by rw [he]; infer_instance
  exact (epi_comp_iff_of_isIso _ ((K.sc n).mapHomologyIso F).hom).mp this

/-- The literal cone of one global finite-free single attachment lowers the
upper cohomological bound on every principal in a finite family. -/
lemma exists_finiteFree_single_lowering_on_principals
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (s : Finset R)
    (hbound : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) n)
    (hfinite : ∀ r : s, Module.Finite (Localization.Away r.val)
      (((localize r.val (.up ℤ)).obj K).homology n)) :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K),
      ∀ r : s, Epi (homologyMap ((localize r.val (.up ℤ)).map f) n) ∧
        CochainComplex.IsLE ((localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)) (n-1) :=
          by
  obtain ⟨m, f, hf⟩ := exists_finiteFree_single_epi_homology_on_principals K n s hfinite
  refine ⟨m, f, fun r => ⟨hf r, ?_⟩⟩
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  have := hbound r
  have := hf r
  have : CochainComplex.IsLE ((localize r.val (.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (Fin m → R)))) n := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (CochainComplex.exactAt_of_isLE
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (Fin m → R))) n i hi).map F
  have := Quillen.CochainComplex.mappingCone_isLE_of_epi_top_homology
    ((localize r.val (.up ℤ)).map f) n
  exact CochainComplex.isLE_of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f F).symm (n-1)

end Quillen.ModuleComplex

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard

/-- A genuine bounded finite-projective derived model makes the highest
original homology finite, without any global termwise finiteness assumption. -/
lemma finite_top_homology_of_moduleStrictPerfect_derived_model (R : CommRingCat.{u})
    (K : ModuleComplex R) (n : ℤ) [K.IsLE n]
    (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj P) :
    Module.Finite R (K.homology n) := by
  have : P.IsLE n := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e n
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hP
  have := Quillen.ModuleComplex.finite_top_homology_of_boundedAbove_finite_projective
    P n b (fun i hi => hb i (Or.inr hi)) (fun i => (hp i).1)
    (fun i => by let := (hp i).2; infer_instance)
  let eH : K.homology n ≅ P.homology n :=
    ((DerivedCategory.homologyFunctorFactors _ n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app P
  exact Module.Finite.equiv eH.toLinearEquiv.symm

/-- Actual principal-local perfect models on any finite family admit one
global finite-free attachment. Its literal cone lowers all local upper bounds
and preserves the given common lower term bound. The family need not cover
the affine base. -/
lemma exists_finiteFree_single_lowering_finite_principal_models
    (R : CommRingCat.{u}) (K : ModuleComplex R) (a n : ℤ) (han : a < n)
    (s : Finset R)
    (hbound : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) n)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K),
      (∀ r : s, Epi (homologyMap ((localize r.val (.up ℤ)).map f) n) ∧
        CochainComplex.IsLE ((localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)) (n-1)) ∧
      ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
        moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
        (∀ i, i < a → IsZero (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj
          (CochainComplex.mappingCone f)) ≅ DerivedCategory.Q.obj P) := by
  have hfinite (r : s) : Module.Finite (Localization.Away r.val)
      (((localize r.val (.up ℤ)).obj K).homology n) := by
    have := hbound r
    obtain ⟨P, hP, _, ⟨e⟩⟩ := hlocal r
    exact finite_top_homology_of_moduleStrictPerfect_derived_model
      (CommRingCat.of (Localization.Away r.val)) _ n P hP e
  obtain ⟨m, f, hf⟩ := Quillen.ModuleComplex.exists_finiteFree_single_lowering_on_principals
    K n s hbound hfinite
  exact ⟨m, f, hf, principal_perfect_models_mappingCone_single R K a n han s hlocal _ f⟩

end Quillen.PerfectComplexes.Affine
