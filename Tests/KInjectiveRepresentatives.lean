/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.KInjectiveRepresentatives
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.InjectiveCounit

/-!
# K-injective representative regression statements

Records homotopies between chain representatives of derived arrows into K-injective
complexes and preservation of a factorization homotopy by additive coefficient
functors. Other statements concern preservation of quasi-isomorphisms between
lower-bounded injective complexes by scheme pushforward and affine global sections.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w u' v'
namespace Tests.KInjectiveRepresentatives
open Quillen.CochainComplex

/-- A prescribed original factorization remains homotopic after any additive coefficient functor. -/
theorem original_factorization_after_coefficients
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    {A B I : CochainComplex C ℤ} [I.IsKInjective] (s : A ⟶ B) (t : A ⟶ I)
    (α : DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj I)
    (h : DerivedCategory.Q.map s ≫ α = DerivedCategory.Q.map t) :
    ∃ f : B ⟶ I, DerivedCategory.Q.map f = α ∧ Nonempty (Homotopy
      (((F.mapHomologicalComplex (.up ℤ)).map s) ≫ ((F.mapHomologicalComplex (.up ℤ)).map f))
      ((F.mapHomologicalComplex (.up ℤ)).map t)) := by
  obtain ⟨f, hf, ⟨H⟩⟩ := exists_chain_factorization_up_to_homotopy_into_isKInjective s t α h
  exact ⟨f, hf, ⟨by simpa only [Functor.map_comp] using F.mapHomotopy H⟩⟩

/-- Two actual representatives of the unchanged derived arrow are genuinely homotopic. -/
theorem original_representatives_homotopic
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K I : CochainComplex C ℤ} [I.IsKInjective]
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I)
    (f g : K ⟶ I) (hf : DerivedCategory.Q.map f = α) (hg : DerivedCategory.Q.map g = α) :
    Nonempty (Homotopy f g) :=
  ⟨homotopyOfDerivedEqOfIsKInjective f g (hf.trans hg.symm)⟩

/-- Any original scheme direct image preserves weak maps between actual injective models. -/
theorem original_scheme_pushforward {U X : Scheme.{u}} (j : U ⟶ X)
    {I J : Quillen.PerfectComplexes.Complex U} (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (hJ : ∀ n, n < b → IsZero (J.X n))
    (iI : ∀ n, Injective (I.X n)) (iJ : ∀ n, Injective (J.X n))
    (f : I ⟶ J) [QuasiIso f] :
    QuasiIso ((Quillen.PerfectComplexes.pushforwardComplex j).map f) :=
  quasiIso_map_of_lowerBounded_injective (Scheme.Modules.pushforward j) a b hI hJ iI iJ f

/-- Actual affine global sections preserve these original weak maps with no QC-homology premise. -/
theorem original_sections_without_qc (R : CommRingCat.{u})
    {I J : Quillen.PerfectComplexes.Complex (Spec R)} (a b : ℤ)
    (hI : ∀ n, n < a → IsZero (I.X n)) (hJ : ∀ n, n < b → IsZero (J.X n))
    (iI : ∀ n, Injective (I.X n)) (iJ : ∀ n, Injective (J.X n))
    (f : I ⟶ J) [QuasiIso f] :
    QuasiIso ((Quillen.PerfectComplexes.Affine.sectionsComplex R).map f) :=
  quasiIso_map_of_lowerBounded_injective moduleSpecΓFunctor a b hI hJ iI iJ f
end Tests.KInjectiveRepresentatives
