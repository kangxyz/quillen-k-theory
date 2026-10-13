/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIterateNullTimeSlice

/-!
# Consumers of the original iterated null-time formula

These clients retain the original cone cylinder, degree-zero values and independent structure
time. The last client is the precise cylinder equation used to propagate the proved supported
seed/null square; its hypothesis is the initial whole square, not a family of iterate squares.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u v w
namespace QuillenTest.StrictDiagramIterateNullTimeSlice

open Quillen
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ G} {b : G ⟶ K}
    (H : DiagramNullHomotopy a b)

/-- The original cone cylinder descends to the actual iterate of the initial time slice. -/
theorem originalConeCylinder (n : ℕ) (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space m) :
    (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
        (((strictDiagramIterate Q n).map b).app X)
        ((strictDiagramIterateNull Q H n).homotopy X)).map m
      (ReducedMappingCone.cylinder
        ((((strictDiagramIterate Q n).obj F).obj X).point m)
        ((((strictDiagramIterate Q n).obj G).obj X).point m)
        ((((strictDiagramIterate Q n).map a).app X).map m) (r, x)) =
      (((strictDiagramIterate Q n).map
        (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
          H.homotopy H.naturality r)).app X).map m x := by
  rw [mappingConeDesc_cylinder, strictDiagramIterateNull_level]

/-- In degree zero, the same actual slice commutes with an arbitrary original coefficient map. -/
theorem originalCoefficientZero (n : ℕ) {X Y : C} (f : X ⟶ Y) (r : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space 0) :
    (((strictDiagramIterate Q n).obj K).map f).map 0
        ((((strictDiagramIterate Q n).map
          (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
            H.homotopy H.naturality r)).app X).map 0 x) =
      ((strictDiagramIterateNull Q H n).homotopy Y).level 0
        (r, (((strictDiagramIterate Q n).obj F).map f).map 0 x) := by
  rw [← strictDiagramIterateNull_level]
  exact (strictDiagramIterateNull Q H n).naturality f 0 r x

/-- The original structure-loop time is independent of the retained null time. -/
theorem originalStructureTime (n : ℕ) (X : C) (m : ℕ) (r t : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space m) :
    (((strictDiagramIterate Q n).map
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        H.homotopy H.naturality r)).app X).map (m + 1)
      ((((strictDiagramIterate Q n).obj F).obj X).structureMap m x t) =
    (((strictDiagramIterate Q n).obj K).obj X).structureMap m
      (((strictDiagramIterateNull Q H n).homotopy X).level m (r, x)) t := by
  rw [← strictDiagramIterateNull_level]
  exact ((strictDiagramIterateNull Q H n).homotopy X).comm m r x t

/-- The supported seed assembly needs this same-height equation on the original cone cylinder. -/
theorem originalTransitionCylinder
    (σ : F ⟶ (strictDiagramFunctor Q).obj F)
    (τ : K ⟶ (strictDiagramFunctor Q).obj K)
    (hseed : ∀ r, σ ≫ (strictDiagramFunctor Q).map
      (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K) H.homotopy H.naturality r) =
      diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K) H.homotopy H.naturality r ≫ τ)
    (n : ℕ) (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space m) :
    (mappingConeDesc (((strictDiagramIterate Q (n + 1)).map a).app X)
        (((strictDiagramIterate Q (n + 1)).map b).app X)
        ((strictDiagramIterateNull Q H (n + 1)).homotopy X)).map m
      (ReducedMappingCone.cylinder
        ((((strictDiagramIterate Q (n + 1)).obj F).obj X).point m)
        ((((strictDiagramIterate Q (n + 1)).obj G).obj X).point m)
        ((((strictDiagramIterate Q (n + 1)).map a).app X).map m)
        (r, ((strictDiagramTransition Q σ n).app X).map m x)) =
      ((strictDiagramTransition Q τ n).app X).map m
        ((mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
          (((strictDiagramIterate Q n).map b).app X)
          ((strictDiagramIterateNull Q H n).homotopy X)).map m
          (ReducedMappingCone.cylinder
            ((((strictDiagramIterate Q n).obj F).obj X).point m)
            ((((strictDiagramIterate Q n).obj G).obj X).point m)
            ((((strictDiagramIterate Q n).map a).app X).map m) (r, x))) := by
  simp only [mappingConeDesc_cylinder]
  exact strictDiagramIterateNull_transition Q H σ τ hseed n X m r x

end QuillenTest.StrictDiagramIterateNullTimeSlice
