/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalMapFactorization
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory

/-! Semantic consumers of original strict principal-open map factorization. -/
@[expose] public section

open Quillen.CochainComplex
open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex.PrincipalLocalization
open Quillen.PerfectComplexes.Affine
attribute [local instance] Abelian.hasFiniteBiproducts
namespace QuillenTest.PrincipalMapFactorization

open Quillen

/-- The generic construction retains the old witness exactly on its summand,
even for additive functors that are not assumed exact. -/
theorem actual_witness_summand_preserved
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u₁} [Category.{v₁} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {A E : CochainComplex C ℤ} (a : A ⟶ E)
    {B : CochainComplex D ℤ} (q : (F.mapHomologicalComplex (.up ℤ)).obj E ⟶ B)
    [QuasiIso q] (f : (F.mapHomologicalComplex (.up ℤ)).obj A ⟶ B)
    (H : Homotopy ((F.mapHomologicalComplex (.up ℤ)).map a ≫ q) f) :
    ∃ p : (F.mapHomologicalComplex (.up ℤ)).obj (mapCylinder A E) ⟶ B,
      (∀ i, IsIso (homologyMap p i)) ∧
      (F.mapHomologicalComplex (.up ℤ)).map (mapCylinderInclusion a) ≫ p = f ∧
      (F.mapHomologicalComplex (.up ℤ)).map (biprod.inl : E ⟶ mapCylinder A E) ≫ p = q := by
  obtain ⟨p, hp, hf, hq⟩ := exists_mapCylinder_strictification F a q f H
  let := hp
  exact ⟨p, fun _ => inferInstance, hf, hq⟩

/-- The original-ring intermediate object is genuinely K-projective, while
the original localized target and exact triangle remain unchanged. -/
theorem actual_KProjective_module_factorization (R : CommRingCat.{u}) (r : R)
    {A E : ModuleComplex R} (hA : moduleStrictPerfect R A) (hE : moduleStrictPerfect R E)
    {B : ModuleComplex (.of (Localization.Away r))}
    (q : (localize r (.up ℤ)).obj E ⟶ B) [QuasiIso q]
    (f : (localize r (.up ℤ)).obj A ⟶ B) :
    ∃ (M : ModuleComplex R) (a : A ⟶ M) (p : (localize r (.up ℤ)).obj M ⟶ B),
      M.IsKProjective ∧ QuasiIso p ∧ (localize r (.up ℤ)).map a ≫ p = f := by
  obtain ⟨M, a, p, hM, hp, hf⟩ := exists_principal_module_map_factorization R r hA hE q f
  exact ⟨M, a, p, isKProjective_of_moduleStrictPerfect R hM, hp, hf⟩

/-- A termwise-QC target in the original all-perfect category is retained
literally, while the intermediate object is proved to be original strict perfect. -/
theorem actual_perfect_target_factorization (R : CommRingCat.{u}) (r : R)
    (A E : StrictPerfect (Spec R))
    (B : Perfect (Spec (.of (Localization.Away r))))
    (hB : ∀ i, (B.obj.X i).IsQuasicoherent)
    (q : (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
      ((strictToPerfect _).obj E) ⟶ B) (hq : (perfectWaldhausen _).weq q)
    (f : (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
      ((strictToPerfect _).obj A) ⟶ B) :
    ∃ (M : StrictPerfect (Spec R))
      (a : (strictToPerfect _).obj A ⟶ (strictToPerfect _).obj M)
      (p : (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
        ((strictToPerfect _).obj M) ⟶ B),
      (perfectWaldhausen _).weq p ∧
        (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map a ≫
          p = f := by
  have : QuasiIso q.hom := hq
  obtain ⟨M, a, p, hp, hf⟩ := exists_principal_geometric_map_factorization R r A E hB q.hom f.hom
  exact ⟨M, ObjectProperty.homMk a, ObjectProperty.homMk p, hp, ObjectProperty.hom_ext _ hf⟩

/-- The literal strict-category factorization computes the original source
map on every homology object with its actual weak comparison. -/
theorem actual_strict_factorization_homology (R : CommRingCat.{u}) (r : R)
    {A : StrictPerfect (Spec R)} {B : StrictPerfect (Spec (.of (Localization.Away r)))}
    (f : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj A ⟶
      B)
    (E : StrictPerfect (Spec R))
    (q : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E ⟶
      B)
    (hq : (strictWaldhausen _).weq q) :
    ∃ (M : StrictPerfect (Spec R)) (a : A ⟶ M)
      (p : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj M
        ⟶ B),
      QuasiIso p.hom ∧ ∀ i,
        homologyMap ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
          r)).map a.hom) i ≫
          homologyMap p.hom i = homologyMap f.hom i := by
  obtain ⟨M, a, p, hp, hf⟩ := exists_principal_strict_map_factorization R r f E q hq
  have : QuasiIso p.hom := hp
  refine ⟨M, a, p, this, fun i => ?_⟩
  have hf' : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map a.hom
    ≫ p.hom = f.hom :=
    congrArg (fun t => t.hom) hf
  simpa only [homologyMap_comp] using congrArg (fun t => homologyMap t i) hf'

end QuillenTest.PrincipalMapFactorization
