/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PrincipalModuleFactorization
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Affine.Comparison

/-!
# Actual strict principal-open geometric map factorization

Original affine reconstruction and the natural localization/restriction
comparison transport the proved module factorization to the original geometric
restriction. Strict sources and strict comparison witnesses suffice for every
termwise quasicoherent target. The final theorem is phrased in the literal
strict-perfect categories with their original Waldhausen weak predicates.
No arbitrary locally-perfect strictification or all-perfect App2 is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

/-- The original geometric triangle admits actual strict factorization for
strict affine source/witness and any termwise quasicoherent target. -/
theorem exists_principal_geometric_map_factorization (R : CommRingCat.{u}) (r : R)
    (A E : StrictPerfect (Spec R))
    {B : CochainComplex (Spec (.of (Localization.Away r))).Modules ℤ}
    (hB : ∀ i, (B.X i).IsQuasicoherent)
    (q : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
      B) [QuasiIso q]
    (f : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj A.obj ⟶
      B) :
    ∃ (M : StrictPerfect (Spec R)) (a : A.obj ⟶ M.obj)
      (p : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj M.obj ⟶
        B),
      QuasiIso p ∧ (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map
        a ≫ p = f := by
  let S := CommRingCat.of (Localization.Away r)
  let L := localize r (.up ℤ)
  let G := associatedComplex S
  let J := restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
  let K := (sectionsComplex R).obj A.obj
  let N := (sectionsComplex R).obj E.obj
  let T := (sectionsComplex S).obj B
  let eA : (associatedComplex R).obj K ≅ A.obj := associatedSectionsIso R A.property
  let eE : (associatedComplex R).obj N ≅ E.obj := associatedSectionsIso R E.property
  let eB : G.obj T ≅ B := associatedSectionsIsoOfQuasicoherent S B hB
  let e := principalRestrictionAssociatedComplexIso R r
  let uA : G.obj (L.obj K) ≅ J.obj A.obj := e.app K ≪≫ J.mapIso eA
  let uE : G.obj (L.obj N) ≅ J.obj E.obj := e.app N ≪≫ J.mapIso eE
  let : G.Full := associatedComplex_full S
  obtain ⟨qM, hqM⟩ := G.map_surjective (uE.hom ≫ q ≫ eB.inv)
  obtain ⟨fM, hfM⟩ := G.map_surjective (uA.hom ≫ f ≫ eB.inv)
  have : QuasiIso (G.map qM) := by rw [hqM]; infer_instance
  have : QuasiIso qM := (quasiIso_associated_iff S qM).mp inferInstance
  obtain ⟨M, a, p, hM, hp, hcomm⟩ := exists_principal_module_map_factorization R r
    (moduleStrictPerfect_sections R A.property) (moduleStrictPerfect_sections R E.property) qM fM
  let pa : J.obj ((associatedComplex R).obj M) ⟶ B :=
    (e.app M).inv ≫ G.map p ≫ eB.hom
  have : QuasiIso (G.map p) := (quasiIso_associated_iff S p).mpr hp
  refine ⟨⟨(associatedComplex R).obj M, strictPerfect_associated R hM⟩,
    eA.inv ≫ (associatedComplex R).map a, pa, inferInstance, ?_⟩
  change J.map (eA.inv ≫ (associatedComplex R).map a) ≫
    (e.app M).inv ≫ G.map p ≫ eB.hom = f
  have hn : J.map ((associatedComplex R).map a) ≫ (e.app M).inv =
      (e.app K).inv ≫ G.map (L.map a) := e.inv.naturality a
  rw [J.map_comp]
  simp only [← Category.assoc]
  rw [Category.assoc (J.map eA.inv), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map (L.map a)) (G.map p), ← G.map_comp, hcomm, hfM]
  simp [uA, Category.assoc]

/-- Restricted map factorization in the original strict-perfect categories,
with the literal principal restriction and original Waldhausen weak predicates. -/
theorem exists_principal_strict_map_factorization (R : CommRingCat.{u}) (r : R)
    {A : StrictPerfect (Spec R)}
    {B : StrictPerfect (Spec (.of (Localization.Away r)))}
    (f : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj A ⟶
      B)
    (E : StrictPerfect (Spec R))
    (q : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E ⟶
      B)
    (hq : (strictWaldhausen _).weq q) :
    ∃ (M : StrictPerfect (Spec R)) (a : A ⟶ M)
      (p : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj M
        ⟶ B),
      (strictWaldhausen _).weq p ∧
        (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map a ≫
          p = f := by
  have : QuasiIso q.hom := hq
  have hB (i : ℤ) : (B.obj.X i).IsQuasicoherent := by
    let := B.property.2 i
    infer_instance
  obtain ⟨M, a, p, hp, hcomm⟩ :=
    exists_principal_geometric_map_factorization R r A E hB q.hom f.hom
  refine ⟨M, ObjectProperty.homMk a, ObjectProperty.homMk p, hp, ?_⟩
  exact ObjectProperty.hom_ext _ hcomm

end Quillen.PerfectComplexes.Affine
