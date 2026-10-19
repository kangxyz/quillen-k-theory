/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientDoubleNegativeRepresentatives
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionTelescope
public import Quillen.KTheory.Bass.ModelDiagramBottomNaturality

/-!
# Original bottom representatives through actual section restriction

The same global-to-coefficient restriction preserves the original Laurent
inclusion and genuine inverse successor shift. Its proved stable inverse can
therefore be moved across each original bottom representative without changing
the negative class map or choosing another quotient identification.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent

universe u

namespace Quillen.PerfectComplexes.CoefficientNegativeRepresentatives

open GlobalSectionChangeIndex

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The global row retains the same Laurent inclusion and inverse signed successor. -/
def globalBottomStep (i : ℕ) (a : Under R) :
    (globalDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ))).obj
        ((laurentUnderFunctor R).obj a) ⟶
      (globalDiagram P (i + 1) ⋙ stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).obj a :=
  (stableHomotopyFunctor (-(i : ℤ))).map
      (mappingConeInclusion (StrictSquare.comparison
        (modelDiagramTwoChartSquare (globalRow P) i a))) ≫
    (modelDiagramBottomSuccessorIso (globalRow P) i).inv.app a

/-- Actual restriction preserves both original maps in every bottom representative. -/
@[reassoc]
theorem globalBottomStep_restriction (i : ℕ) (a : Under R) :
    (stableHomotopyFunctor (-(i : ℤ))).map
        ((finiteRestriction P i).app ((laurentUnderFunctor R).obj a)) ≫ bottomStep P i a =
      globalBottomStep P i a ≫ (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((finiteRestriction P (i + 1)).app a) := by
  let α := Functor.whiskerRight (rowRestriction P) prespectrumFunctor
  apply (cancel_mono
    ((modelDiagramBottomSuccessorIso (boundedFlatCoefficientSectionModelRow P) i).hom.app a)).mp
  dsimp only [bottomStep, globalBottomStep]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [show (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((finiteRestriction P (i + 1)).app a) ≫
      (modelDiagramBottomSuccessorIso (boundedFlatCoefficientSectionModelRow P) i).hom.app a =
    (modelDiagramBottomSuccessorIso (globalRow P) i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeMap (strictSquareComparisonFunctor.map
          (modelDiagramTwoChartSquareTransformation α i a))) from
    modelDiagramBottomSuccessorIso_map α i a]
  simp only [Iso.inv_hom_id_app_assoc]
  exact Quillen.Bass.TwoChartStable.comparisonConeMap_inclusion
    (modelDiagramTwoChartSquareTransformation α i a) (-(i : ℤ))

private theorem inverse_square {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (g : D ⟶ E) [IsIso f] [IsIso g]
    (a : A ⟶ D) (b : B ⟶ E) (h : f ≫ b = a ≫ g) :
    b ≫ inv g = inv f ≫ a := by
  apply (cancel_mono g).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

/-- Only the already proved inverse of actual restriction is moved across the original step. -/
@[reassoc]
theorem bottomStep_inverseRestriction (i : ℕ) (a : Under R) :
    bottomStep P i a ≫ inv
        (I := finiteRestriction_isStableEquivalence P (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction P (i + 1)).app a)) =
      inv (I := finiteRestriction_isStableEquivalence P i ((laurentUnderFunctor R).obj a)
        (-(i : ℤ)))
        ((stableHomotopyFunctor (-(i : ℤ))).map
          ((finiteRestriction P i).app ((laurentUnderFunctor R).obj a))) ≫
        globalBottomStep P i a := by
  let := finiteRestriction_isStableEquivalence P i ((laurentUnderFunctor R).obj a) (-(i : ℤ))
  let := finiteRestriction_isStableEquivalence P (i + 1) a (-((i + 1 : ℕ) : ℤ))
  exact inverse_square _ _ _ _ (globalBottomStep_restriction P i a)

private theorem two_step_transport {C : Type*} [Category C]
    {A B D E F G H I : C} (q : A ⟶ B) (z : B ⟶ D) (v : D ⟶ E)
    (c : A ⟶ F) (b₀ : F ⟶ G) (b₁ : G ⟶ D) (u : G ⟶ H)
    (w : F ⟶ I) (g₀ : I ⟶ H) (g₁ : H ⟶ E)
    (hq : q ≫ z = c ≫ b₀ ≫ b₁) (h₀ : b₀ ≫ u = w ≫ g₀)
    (h₁ : b₁ ≫ v = u ≫ g₁) : q ≫ z ≫ v = c ≫ w ≫ g₀ ≫ g₁ := by
  rw [← Category.assoc q, hq]
  simp only [Category.assoc]
  rw [h₁, ← Category.assoc b₀, h₀]
  simp only [Category.assoc]

/-- The original double quotient keeps its class map when actual restriction is inverted. -/
@[reassoc]
theorem doubleLaurentQuotient_inverseRestriction [CompactSpace P.left] (a : Under R) :
    doubleLaurentQuotient P a ≫
      (boundedFlatCoefficientAmbientNegativeKComparison P 2).hom.app a ≫
        inv (I := finiteRestriction_isStableEquivalence P 2 a (-((2 : ℕ) : ℤ)))
          ((stableHomotopyFunctor (-((2 : ℕ) : ℤ))).map ((finiteRestriction P 2).app a)) =
      (boundedFlatCoefficientAmbientNegativeKComparison P 0).hom.app
          ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ≫
        inv (I := finiteRestriction_isStableEquivalence P 0
          ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) (-((0 : ℕ) : ℤ)))
          ((stableHomotopyFunctor (-((0 : ℕ) : ℤ))).map
            ((finiteRestriction P 0).app
              ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)))) ≫
        globalBottomStep P 0 ((laurentUnderFunctor R).obj a) ≫ globalBottomStep P 1 a := by
  exact two_step_transport _ _ _ _ _ _ _ _ _ _
    (doubleLaurentQuotient_comparison P a)
    (bottomStep_inverseRestriction P 0 ((laurentUnderFunctor R).obj a))
    (bottomStep_inverseRestriction P 1 a)

end Quillen.PerfectComplexes.CoefficientNegativeRepresentatives
