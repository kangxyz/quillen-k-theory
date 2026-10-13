/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.InjectivePushforwardAdjunction

/-! # Original injective-target direct-image Hom consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes
namespace QuillenTest.DerivedPushforwardHom

open Quillen

/-- The generic chain formula retains independent categories and independent derived model
  universes. -/
theorem original_generic_chain_adjoint
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
    (K : CochainComplex C ℤ) (I : CochainComplex D ℤ) [I.IsKInjective]
    [_root_.CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I)]
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ I) :
    adj.cochainDerivedHomEquivOfKInjective K I (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I f) :=
  adj.cochainDerivedHomEquivOfKInjective_map K I f

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Both inverse laws hold for the literal original derived objects and all arrows. -/
theorem original_hom_inverse_laws (K : Complex X) (I : Complex U) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj ((pushforwardComplex j).obj I))
    (α : (toDerived U).obj ((restrict j).obj K) ⟶ (toDerived U).obj I) :
    (pushforwardDerivedHomEquiv j K I a hbound hinj).symm
        (pushforwardDerivedHomEquiv j K I a hbound hinj φ) = φ ∧
      pushforwardDerivedHomEquiv j K I a hbound hinj
        ((pushforwardDerivedHomEquiv j K I a hbound hinj).symm α) = α :=
  ⟨AddEquiv.symm_apply_apply _ _, AddEquiv.apply_symm_apply _ _⟩

/-- The original derived map is recovered by actual restriction and the existing direct-image
  counit. -/
theorem original_counit_formula (K : Complex X) (I : Complex U) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj ((pushforwardComplex j).obj I)) :
    pushforwardDerivedHomEquiv j K I a hbound hinj φ = restrictDerivedHom j φ ≫
      (toDerived U).map ((pushforwardComplexRestrictIso j).hom.app I) :=
  pushforwardDerivedHomEquiv_eq_original_counit j K I a hbound hinj φ

/-- A source denominator remains the actual original derived map in the transpose equation. -/
theorem original_denominator_square {K K' : Complex X} (I : Complex U) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (q : K' ⟶ K)
    (α : (toDerived U).obj ((restrict j).obj K) ⟶ (toDerived U).obj I) :
    (pushforwardDerivedHomEquiv j K' I a hbound hinj).symm
        ((toDerived U).map ((restrict j).map q) ≫ α) =
      (toDerived X).map q ≫ (pushforwardDerivedHomEquiv j K I a hbound hinj).symm α := by
  rw [← restrictDerivedHom_map]
  exact pushforwardDerivedHomEquiv_symm_precomp j I a hbound hinj _ α

/-- A local weak chain input gives the genuine original globally defined adjoint, weak on the open.
  -/
theorem original_local_weak_adjoint (K : Complex X) (I : Complex U) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    QuasiIso ((restrict j).map ((restrictPushforwardComplexAdjunction j).homEquiv K I q)) ∧
      (pushforwardDerivedHomEquiv j K I a hbound hinj).symm ((toDerived U).map q) =
        (toDerived X).map ((restrictPushforwardComplexAdjunction j).homEquiv K I q) :=
  ⟨quasiIso_restrict_chain_adjoint j q, pushforwardDerivedHomEquiv_symm_map j K I a hbound hinj q⟩

/-- Independent injective bounds give original target naturality; the right adjoint need not be
  exact. -/
theorem original_independent_target_bounds (K : Complex X) (I J : Complex U) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj ((pushforwardComplex j).obj I))
    (f : I ⟶ J) [QuasiIso f] :
    IsIso ((toDerived X).map ((pushforwardComplex j).map f)) ∧
      pushforwardDerivedHomEquiv j K J b hJ iJ (φ ≫ (toDerived X).map ((pushforwardComplex j).map
        f)) =
        pushforwardDerivedHomEquiv j K I a hI iI φ ≫ (toDerived U).map f := by
  have : QuasiIso ((pushforwardComplex j).map f) :=
    Quillen.CochainComplex.quasiIso_map_of_lowerBounded_injective (Scheme.Modules.pushforward j)
      a b hI hJ iI iJ f
  exact ⟨inferInstance, pushforwardDerivedHomEquiv_postcomp j K I J a b hI iI hJ iJ φ f⟩

/-- Original local derived arrows have global chain lifts with their exact derived image. -/
theorem original_global_chain_lift (K : Complex X) (I : Complex U) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (α : (toDerived U).obj ((restrict j).obj K) ⟶ (toDerived U).obj I) :
    ∃ f : K ⟶ (pushforwardComplex j).obj I,
      pushforwardDerivedHomEquiv j K I a hbound hinj ((toDerived X).map f) = α :=
  exists_pushforward_chain_adjoint j K I a hbound hinj α

end QuillenTest.DerivedPushforwardHom
