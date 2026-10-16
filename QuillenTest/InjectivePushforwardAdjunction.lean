/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.InjectivePushforwardAdjunction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Original injective-target direct-image Hom consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w w'
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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
theorem original_hom_inverse_laws (K : CochainComplex X.Modules ℤ) (I : CochainComplex U.Modules ℤ)
    (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I))
    (α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj I) :
    (pushforwardDerivedHomEquiv j K I a hbound hinj).symm
        (pushforwardDerivedHomEquiv j K I a hbound hinj φ) = φ ∧
      pushforwardDerivedHomEquiv j K I a hbound hinj
        ((pushforwardDerivedHomEquiv j K I a hbound hinj).symm α) = α :=
  ⟨AddEquiv.symm_apply_apply _ _, AddEquiv.apply_symm_apply _ _⟩

/-- The original derived map is recovered by actual restriction and the existing direct-image
  counit. -/
theorem original_counit_formula (K : CochainComplex X.Modules ℤ) (I : CochainComplex U.Modules ℤ)
    (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I)) :
    pushforwardDerivedHomEquiv j K I a hbound hinj φ = restrictDerivedHom j φ ≫
      (DerivedCategory.Q (C := U.Modules)).map ((pushforwardComplexRestrictIso j).hom.app I) :=
  pushforwardDerivedHomEquiv_eq_original_counit j K I a hbound hinj φ

/-- A source denominator remains the actual original derived map in the transpose equation. -/
theorem original_denominator_square {K K' : CochainComplex X.Modules ℤ}
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (q : K' ⟶ K)
    (α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj I) :
    (pushforwardDerivedHomEquiv j K' I a hbound hinj).symm
        ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ α) =
      (DerivedCategory.Q (C := X.Modules)).map q ≫
        (pushforwardDerivedHomEquiv j K I a hbound hinj).symm α := by
  rw [← restrictDerivedHom_map]
  exact pushforwardDerivedHomEquiv_symm_precomp j I a hbound hinj _ α

/-- A local weak chain input gives the genuine original globally defined adjoint, weak on the open.
  -/
theorem original_local_weak_adjoint (K : CochainComplex X.Modules ℤ)
    (I : CochainComplex U.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (q : (restrict j).obj K ⟶ I) [QuasiIso q] :
    QuasiIso ((restrict j).map ((restrictPushforwardComplexAdjunction j).homEquiv K I q)) ∧
      (pushforwardDerivedHomEquiv j K I a hbound hinj).symm
        ((DerivedCategory.Q (C := U.Modules)).map q) =
        (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv
          K I q) :=
  ⟨quasiIso_restrict_chain_adjoint j q, pushforwardDerivedHomEquiv_symm_map j K I a hbound hinj q⟩

/-- Independent injective bounds give original target naturality; the right adjoint need not be
  exact. -/
theorem original_independent_target_bounds (K : CochainComplex X.Modules ℤ)
    (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I))
    (f : I ⟶ J) [QuasiIso f] :
    IsIso ((DerivedCategory.Q (C := X.Modules)).map ((pushforwardComplex j).map f)) ∧
      pushforwardDerivedHomEquiv j K J b hJ iJ (φ ≫ (DerivedCategory.Q (C := X.Modules)).map
        ((pushforwardComplex j).map
        f)) =
        pushforwardDerivedHomEquiv j K I a hI iI φ ≫
          (DerivedCategory.Q (C := U.Modules)).map f := by
  have : QuasiIso ((pushforwardComplex j).map f) :=
    _root_.CochainComplex.quasiIso_map_of_lowerBounded_injective (Scheme.Modules.pushforward j)
      a b hI hJ iI iJ f
  exact ⟨inferInstance, pushforwardDerivedHomEquiv_postcomp j K I J a b hI iI hJ iJ φ f⟩

/-- Original local derived arrows have global chain lifts with their exact derived image. -/
theorem original_global_chain_lift (K : CochainComplex X.Modules ℤ) (I : CochainComplex U.Modules ℤ)
    (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (α : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj I) :
    ∃ f : K ⟶ (pushforwardComplex j).obj I,
      pushforwardDerivedHomEquiv j K I a hbound hinj ((DerivedCategory.Q (C := X.Modules)).map f)
        = α :=
  exists_pushforward_chain_adjoint j K I a hbound hinj α

end QuillenTest.DerivedPushforwardHom
