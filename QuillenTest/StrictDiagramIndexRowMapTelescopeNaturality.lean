/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIndexRowMapTelescopeNaturality

/-!
# Forward row telescope comparison regressions

The whole input square acts on actual stable classes in every signed degree. Under the
explicit T1 and finite-stability hypotheses the same forward map is bijective there,
without a natural inverse to the row transformation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u₁ v₁ u₂ v₂ w
namespace QuillenTest.StrictDiagramIndexRowMapTelescopeNaturality
open StrictDiagramIndexChange StrictDiagramIndexRowMap

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F F' : D ⥤ LoopPrespectrum.{w}} {G G' : C ⥤ LoopPrespectrum.{w}}
    (ρ : K ⋙ F ⟶ G) (ρ' : K ⋙ F' ⟶ G') (τ : F ⟶ F') (σ : G ⟶ G')
    (hrow : Functor.whiskerLeft K τ ≫ ρ' = ρ ≫ σ)
    (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₂' : F' ⟶ (strictDiagramFunctor Q₂).obj F')
    (η₁ : G ⟶ (strictDiagramFunctor Q₁).obj G)
    (η₁' : G' ⟶ (strictDiagramFunctor Q₁).obj G')
    (h₂ : η₂ ≫ (strictDiagramFunctor Q₂).map τ = τ ≫ η₂')
    (h₁ : η₁ ≫ (strictDiagramFunctor Q₁).map σ = σ ≫ η₁')
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom ≫
      (strictDiagramFunctor Q₁).map ρ = ρ ≫ η₁)
    (hseed' : Functor.whiskerLeft K η₂' ≫ (iso K Q₁ Q₂ α F').hom ≫
      (strictDiagramFunctor Q₁).map ρ' = ρ' ≫ η₁')

include hrow in
/-- General forward rows preserve the complete square on stable classes of any signed degree. -/
theorem stable_class_square (X : C) (d : ℤ)
    (z : stableHomotopyGroup ((telescope Q₂ η₂).obj (K.obj X)) d) :
    (stableHomotopyFunctor d).map ((telescopeMap K Q₁ Q₂ α ρ' η₂' η₁' hseed').app X)
        ((stableHomotopyFunctor d).map
          ((StrictDiagramIndexRow.seedTelescopeMap Q₂ η₂ η₂' τ h₂).app (K.obj X)) z) =
      (stableHomotopyFunctor d).map
        ((StrictDiagramIndexRow.seedTelescopeMap Q₁ η₁ η₁' σ h₁).app X)
        ((stableHomotopyFunctor d).map
          ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X) z) := by
  have h := NatTrans.congr_app (telescopeMap_naturality K Q₁ Q₂ α ρ ρ' τ σ hrow
    η₂ η₂' η₁ η₁' h₂ h₁ hseed hseed') X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have hstable := congrArg ((stableHomotopyFunctor d).map) h
  simp only [Functor.map_comp] at hstable
  exact ConcreteCategory.congr_hom hstable z

/-- The actual forward comparison gives a bijection in every signed stable degree. -/
theorem stable_class_bijective (X : C)
    [∀ i n, T1Space ((((strictDiagramIterate Q₂ i).obj F).obj (K.obj X)).space n)]
    [∀ i n, T1Space ((((strictDiagramIterate Q₁ i).obj G).obj X).space n)]
    (hfinite : ∀ i, IsStableEquivalence ((finiteMap K Q₁ Q₂ α ρ i).app X)) (d : ℤ) :
    Function.Bijective
      ((stableHomotopyFunctor d).map
        ((telescopeMap K Q₁ Q₂ α ρ η₂ η₁ hseed).app X)) := by
  have := telescopeMap_stable K Q₁ Q₂ α ρ η₂ η₁ hseed X hfinite d
  exact ConcreteCategory.bijective_of_isIso _

end QuillenTest.StrictDiagramIndexRowMapTelescopeNaturality
