/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectDerivedEquivalence
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-!
# Perfect approximations on an arbitrary finite principal family

Finite induction attaches actual finite-free singles and composes the
original cone-inclusion maps. The octahedral closure of the existing perfect
derived subcategory proves that the composite has perfect cone. Genuine
module K-projectivity then supplies an actual global bounded finite-projective
source and chain map into the original module complex.

On every selected principal open the literal residual cone is concentrated
at the prescribed common lower term bound. Its original homology is finite
projective over that localization ring and has an actual single-complex
quasi-isomorphism inducing the identity on homology.

The principal family need not cover the affine base. Residual projectivity
is therefore only a local conclusion on these opens. This does not assert
that the global residual cone is perfect, that its homology is globally
projective, or that a vector-bundle complement already splits on the open.
The derived direct-image and finite cohomological-dimension inputs needed
for that later extension theorem remain separate.

See Stacks Project, Tag 08EC, for the perfect-approximation route.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex AlgebraicGeometry

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard

/-- Finite actual cone induction over a finite principal family produces
an original chain map with globally perfect cone and a locally concentrated
remainder. The family need not cover the whole affine scheme. -/
lemma exists_finite_principal_concentrated_remainder
    (R : CommRingCat.{u}) (K : ModuleComplex R) (a b : ℤ) (s : Finset R)
    (hbound : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) b)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (C : ModuleComplex R) (q : K ⟶ C),
      (finiteProjectiveDerivedObjects R).trW (DerivedCategory.Q.map q) ∧
      (∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj C) a) ∧
      ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
        moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
        (∀ i, i < a → IsZero (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj C) ≅ DerivedCategory.Q.obj P)
          := by
  by_cases hab : a ≤ b
  · induction b, hab using Int.leInduction generalizing K with
    | base =>
      refine ⟨K, 𝟙 K, ?_, hbound, hlocal⟩
      rw [CategoryTheory.Functor.map_id]
      exact MorphismProperty.id_mem _ _
    | succ n hn ih =>
      obtain ⟨m, f, hf, hm⟩ :=
        exists_finiteFree_single_lowering_finite_principal_models R K a (n+1)
          (by omega) s hbound hlocal
      have hc (r : s) : CochainComplex.IsLE
          ((localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)) n := by
        simpa using (hf r).2
      obtain ⟨C, q, hq, hb, hmodels⟩ := ih (CochainComplex.mappingCone f) hc hm
      have hu : (finiteProjectiveDerivedObjects R).trW
          (DerivedCategory.Q.map (CochainComplex.mappingCone.inr f)) :=
        ObjectProperty.trW.mk' (finiteProjectiveDerivedObjects R)
          (DerivedCategory.mappingCone_triangle_distinguished f)
          ⟨_, moduleStrictPerfect_single R (n+1) (ModuleCat.of R (Fin m → R)), ⟨Iso.refl _⟩⟩
      refine ⟨C, CochainComplex.mappingCone.inr f ≫ q, ?_, hb, hmodels⟩
      rw [CategoryTheory.Functor.map_comp]
      exact (finiteProjectiveDerivedObjects R).trW.comp_mem _ _ hu hq
  · have hb (r : s) : CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) a := by
      have := hbound r
      exact CochainComplex.isLE_of_le _ b a (by omega)
    refine ⟨K, 𝟙 K, ?_, hb, hlocal⟩
    rw [CategoryTheory.Functor.map_id]
    exact MorphismProperty.id_mem _ _

/-- A chain map with perfect derived cone has an actual bounded finite-projective
fiber model. The original map to its target is the cone inclusion followed by
the displayed original derived isomorphism. -/
lemma exists_moduleStrictPerfect_fiber_of_perfect_cone
    (R : CommRingCat.{u}) {K C : ModuleComplex R} (q : K ⟶ C)
    (hq : (finiteProjectiveDerivedObjects R).trW (DerivedCategory.Q.map q)) :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (e : DerivedCategory.Q.obj (CochainComplex.mappingCone f) ≅ DerivedCategory.Q.obj C),
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr f) ≫ e.hom =
        DerivedCategory.Q.map q := by
  obtain ⟨A, α, δ, hT, hA⟩ :=
    ((finiteProjectiveDerivedObjects R).trW_iff' (DerivedCategory.Q.map q)).mp hq
  obtain ⟨P, hP, ⟨eP⟩⟩ := hA
  have := isKProjective_of_moduleStrictPerfect R hP
  obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective
    (eP.hom ≫ α)
  let eT := isoTriangleOfIso₁₂ _ _
    (DerivedCategory.mappingCone_triangle_distinguished f) hT eP (Iso.refl _)
    (by simpa using hf)
  refine ⟨P, hP, f, Triangle.π₃.mapIso eT, ?_⟩
  simpa [eT] using eT.hom.comm₂

/-- Finite-principal local perfection gives an actual global bounded
finite-projective approximation. Its original mapping cone is cohomologically
at most a on the selected opens and retains actual models supported in degrees
at least a there. No whole-Spec cover or global projectivity of the residual
homology is asserted. -/
lemma exists_moduleStrictPerfect_approximation_on_finite_principals
    (R : CommRingCat.{u}) (K : ModuleComplex R) (a b : ℤ) (s : Finset R)
    (hbound : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) b)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      (∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj
        (CochainComplex.mappingCone f)) a) ∧
      ∀ r : s, ∃ L : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
        moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) L ∧
        (∀ i, i < a → IsZero (L.X i)) ∧
        Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj
          (CochainComplex.mappingCone f)) ≅ DerivedCategory.Q.obj L) := by
  obtain ⟨C, q, hq, hb, hm⟩ :=
    exists_finite_principal_concentrated_remainder R K a b s hbound hlocal
  obtain ⟨P, hP, f, e, _⟩ := exists_moduleStrictPerfect_fiber_of_perfect_cone R q hq
  have er (r : s) : DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj
      (CochainComplex.mappingCone f)) ≅
        DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj C) := by
    let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
    exact (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone f)).symm ≪≫
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app C
  refine ⟨P, hP, f, fun r => ?_, fun r => ?_⟩
  · have := hb r
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso (er r).symm a
  · obtain ⟨L, hL, hl, ⟨eL⟩⟩ := hm r
    exact ⟨L, hL, hl, ⟨er r ≪≫ eL⟩⟩

/-- Concentration at the common lower term bound makes the original homology
finite projective, provided only that single original derived model. -/
lemma finiteProjective_concentrated_homology_of_derived_model
    (R : CommRingCat.{u}) (K : ModuleComplex R) (a : ℤ) [K.IsLE a]
    (P : ModuleComplex R) (hP : moduleStrictPerfect R P)
    (hbelow : ∀ i, i < a → IsZero (P.X i))
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj P) :
    K.IsGE a ∧ Module.Finite R (K.homology a) ∧ Projective (K.homology a) := by
  have : P.IsLE a := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e a
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P a).mpr hbelow
  have hK : K.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  obtain ⟨⟨c, b, hb⟩, hp⟩ := hP
  obtain ⟨hf, hp⟩ := Quillen.ModuleComplex.finiteProjective_homology_of_bounded_model
    P a b hbelow (fun i hi => hb i (Or.inr hi)) (fun i => (hp i).1)
    (fun i => by let := (hp i).2; infer_instance)
  let eH : K.homology a ≅ P.homology a :=
    ((DerivedCategory.homologyFunctorFactors _ a).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ a).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ a).app P
  exact ⟨hK, Module.Finite.equiv eH.toLinearEquiv.symm, Projective.of_iso eH.symm hp⟩

/-- A genuine global perfect approximation on a finite principal family has
an actual single finite-projective comparison to each localized residual cone.
Projectivity is asserted only over those localization rings. -/
lemma exists_moduleStrictPerfect_approximation_with_local_projective_remainder
    (R : CommRingCat.{u}) (K : ModuleComplex R) (a b : ℤ) (s : Finset R)
    (hbound : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) b)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      ∀ r : s,
        let C : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ :=
          (localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)
        C.IsLE a ∧ C.IsGE a ∧ Module.Finite (Localization.Away r.val) (C.homology a) ∧
          Projective (C.homology a) ∧
          ∃ g : (CochainComplex.singleFunctor (ModuleCat.{u} (Localization.Away r.val)) a).obj
              (C.homology a) ⟶ C,
            QuasiIso g ∧ (singleObjHomologySelfIso (.up ℤ) a (C.homology a)).inv ≫
              homologyMap g a = 𝟙 _ := by
  obtain ⟨P, hP, f, hb, hm⟩ :=
    exists_moduleStrictPerfect_approximation_on_finite_principals R K a b s hbound hlocal
  refine ⟨P, hP, f, fun r => ?_⟩
  dsimp only
  have := hb r
  obtain ⟨L, hL, hl, ⟨eL⟩⟩ := hm r
  obtain ⟨hge, hfin, hproj⟩ := finiteProjective_concentrated_homology_of_derived_model
    (CommRingCat.of (Localization.Away r.val)) _ a L hL hl eL
  let C : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ :=
    (localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)
  exact ⟨hb r, hge, hfin, hproj,
    Quillen.ModuleComplex.fromSingleHomologyLift C a (C.homology a) (𝟙 _),
    Quillen.ModuleComplex.quasiIso_fromSingleHomologyLift_id C a,
    Quillen.ModuleComplex.fromSingleHomologyLift_homology C a (C.homology a) (𝟙 _)⟩

end Quillen.PerfectComplexes.Affine
