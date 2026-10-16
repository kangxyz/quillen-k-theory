/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.InjectivePushforwardComparison
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Actual injective-model change consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.InjectiveModelChange

open Quillen

/-- Every additive functor preserves an original derived equality into a K-injective target. -/
theorem original_generic_equality
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] (K L : CochainComplex C ℤ) [L.IsKInjective]
    (f g : K ⟶ L) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) := by
  simpa using congrArg (_root_.CochainComplex.mapDerivedHomOfKInjective F K L) h

/-- Original derived inverse arrows remain actual inverse arrows after any additive functor. -/
theorem original_generic_inverses
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] (K L : CochainComplex C ℤ) [K.IsKInjective] [L.IsKInjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    _root_.CochainComplex.mapDerivedHomOfKInjective F K L e.hom ≫
        _root_.CochainComplex.mapDerivedHomOfKInjective F L K e.inv = 𝟙 _ ∧
      _root_.CochainComplex.mapDerivedHomOfKInjective F L K e.inv ≫
        _root_.CochainComplex.mapDerivedHomOfKInjective F K L e.hom = 𝟙 _ := by
  constructor
  · rw [← _root_.CochainComplex.mapDerivedHomOfKInjective_comp, e.hom_inv_id,
      _root_.CochainComplex.mapDerivedHomOfKInjective_id]
  · rw [← _root_.CochainComplex.mapDerivedHomOfKInjective_comp, e.inv_hom_id,
      _root_.CochainComplex.mapDerivedHomOfKInjective_id]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Zero reflection keeps the actual conjugated restriction, and imposes no condition on the source.
  -/
theorem original_restriction_zero_iff (I J : CochainComplex U.Modules ℤ) (b : ℤ)
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (α : (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj I) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj J)) :
    (DerivedCategory.Q (C := U.Modules)).map ((pushforwardComplexRestrictIso j).inv.app I) ≫
        restrictDerivedHom j α ≫ (DerivedCategory.Q (C := U.Modules)).map
          ((pushforwardComplexRestrictIso j).hom.app J) = 0
          ↔
      α = 0 := by
  rw [← injectivePushforwardHomEquiv_eq j I J b hJ iJ α]
  exact (injectivePushforwardHomEquiv j I J b hJ iJ).map_eq_zero_iff

/-- Both original global units survive genuine model change, including the inverse direction. -/
theorem original_two_replacement_units (K : CochainComplex X.Modules ℤ)
    (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (q : (restrict j).obj K ⟶ I) (r : (restrict j).obj K ⟶ J) [QuasiIso q] [QuasiIso r] :
    ∃ e : (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj I) ≅
        (DerivedCategory.Q (C := X.Modules)).obj ((pushforwardComplex j).obj J),
      (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv K
        I q) ≫ e.hom =
        (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv
          K J r) ∧
      (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv K
        J r) ≫ e.inv =
        (DerivedCategory.Q (C := X.Modules)).map ((restrictPushforwardComplexAdjunction j).homEquiv
          K I q) := by
  obtain ⟨e, h, _⟩ := exists_pushforward_modelIso_of_local_replacements j K I J a b hI iI hJ iJ q r
  refine ⟨e, h, ?_⟩
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The original Hom transpose retains simultaneous arbitrary source and target derived changes. -/
theorem original_two_sided_naturality (K K' : CochainComplex X.Modules ℤ)
    (I J : CochainComplex U.Modules ℤ) (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (iI : ∀ n, Injective (I.X n))
    (hJ : ∀ n, n < b → IsZero (J.X n)) (iJ : ∀ n, Injective (J.X n))
    (δ : (DerivedCategory.Q (C := X.Modules)).obj K' ⟶ (DerivedCategory.Q (C := X.Modules)).obj K)
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((pushforwardComplex j).obj I))
    (β : (DerivedCategory.Q (C := U.Modules)).obj I ⟶ (DerivedCategory.Q (C := U.Modules)).obj J) :
    pushforwardDerivedHomEquiv j K' J b hJ iJ
        (δ ≫ φ ≫ (injectivePushforwardHomEquiv j I J b hJ iJ).symm β) =
      restrictDerivedHom j δ ≫ pushforwardDerivedHomEquiv j K I a hI iI φ ≫ β := by
  rw [pushforwardDerivedHomEquiv_precomp,
    pushforwardDerivedHomEquiv_postcomp_derived j K I J a b hI iI hJ iJ]

end QuillenTest.InjectiveModelChange
