/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PrincipalProjectiveExtension
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedModuleReplacement
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! Semantic consumers of actual projective stabilization and principal extension. -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex Quillen.ModuleComplex.PrincipalLocalization
open Quillen.PerfectComplexes.Affine
attribute [local instance] Abelian.hasFiniteBiproducts
namespace QuillenTest.PrincipalProjectiveExtension

open Quillen

/-- The descended complex is genuinely K-projective over the original ring;
both actual localization maps induce inverse homology isomorphisms. -/
theorem actual_projective_stable_descent {R : Type u} [CommRing R] (r : R)
    (K : CochainComplex (ModuleCat.{u} (Localization.Away r)) ℤ)
    (a b : ℤ) (hbound : ∀ i, i < a ∨ b < i → IsZero (K.X i))
    (hfinite : ∀ i, Module.Finite (Localization.Away r) (K.X i))
    (hprojective : ∀ i, Module.Projective (Localization.Away r) (K.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (e : HomotopyEquiv ((localize r (.up ℤ)).obj P) (K ⊞ K⟦(1 : ℤ)⟧)),
      P.IsKProjective ∧ (∀ i, i < a - 1 ∨ b < i → IsZero (P.X i)) ∧
      ∀ i, homologyMap e.hom i ≫ homologyMap e.inv i = 𝟙 _ := by
  obtain ⟨P, hP, hf, ⟨e⟩⟩ :=
    exists_bounded_finiteFree_stable_descent r K a b hbound hfinite hprojective
  have : P.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff _ _).mpr (fun i hi => hP i (Or.inr hi))
  have (i : ℤ) : Projective (P.X i) := by
    let := (hf i).1
    infer_instance
  refine ⟨P, e, CochainComplex.isKProjective_of_projective P b, hP, fun i => ?_⟩
  rw [← homologyMap_comp, e.homotopyHomInvId.homologyMap_eq, homologyMap_id]

/-- Stabilization is preserved by every additive coefficient functor,
without any exactness or flatness assumption on that functor. -/
theorem stabilization_after_arbitrary_additive_functor
    {R : Type u} [CommRing R] {C : Type*} [Category C] [Abelian C]
    (F : ModuleCat.{u} R ⥤ C) [F.Additive]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (Q : ℤ → ModuleCat.{u} R) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (projectiveStabilizationHomotopyEquiv K Q).hom) :=
  (F.mapHomotopyEquiv (projectiveStabilizationHomotopyEquiv K Q)).quasiIso_hom

/-- The original strict Waldhausen model sees an actual weak equivalence
from a genuinely restricted strict object to the shifted sum. -/
theorem actual_strict_restriction_weak_image (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ (Q : StrictPerfect (Spec R))
      (T : StrictPerfect (Spec (.of (Localization.Away r))))
      (f : (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj Q
        ⟶ T),
      T.obj = (P.obj ⊞ P.obj⟦(1 : ℤ)⟧) ∧ (strictWaldhausen _).weq f := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_principal_strict_extension_after_shift R r P
  have hT : strictPerfect _ (P.obj ⊞ P.obj⟦(1 : ℤ)⟧) :=
    (CategoryTheory.ExactCategory.abelianExactStructure _).prop_biprod _ P.property
      (strictPerfect_shift P.property 1)
  exact ⟨Q, ⟨_, hT⟩, ObjectProperty.homMk e.hom, rfl, e.quasiIso_hom⟩

/-- The actual ambient derived retract yields a genuine split idempotent
on the restriction of an original strict object. -/
theorem actual_derived_split_idempotent (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ (Q : StrictPerfect (Spec R))
      (h : Retract ((DerivedCategory.Q).obj P.obj)
        ((DerivedCategory.Q).obj
          ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
          R r)).obj Q.obj))),
      (h.r ≫ h.i) ≫ (h.r ≫ h.i) = h.r ≫ h.i := by
  obtain ⟨Q, ⟨h⟩⟩ := exists_principal_strict_derived_retract R r P
  exact ⟨Q, h, by simp [Category.assoc]⟩

end QuillenTest.PrincipalProjectiveExtension
