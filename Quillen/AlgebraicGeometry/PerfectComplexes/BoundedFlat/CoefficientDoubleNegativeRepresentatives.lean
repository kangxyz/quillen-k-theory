/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassOriginalNegativeComparison

/-!
# Original double-Laurent representatives at the second finite bottom

The two original Laurent quotient maps, with their actual coefficient-product
isomorphisms, form an epimorphism onto the original second negative group.
Its finite-bottom comparison is the two original cone inclusions interleaved
with the original inverse signed successor shifts. The order and signs are
retained; no permutation of the two Laurent variables is imposed.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent

universe u

namespace Quillen.PerfectComplexes.CoefficientNegativeRepresentatives

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The original Laurent quotient in the actual coefficient row, with its geometric transport. -/
def laurentQuotient (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i).obj
        ((laurentUnderFunctor R).obj a) ⟶
      (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor (i + 1)).obj a :=
  (Bass.negativeKFunctor i).map ((boundedFlatCoefficientLaurentIso P).hom.app a) ≫
    Bass.negativeKπ ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop i

instance laurentQuotient_epi (i : ℕ) (a : Under R) : Epi (laurentQuotient P i a) := by
  dsimp only [laurentQuotient]
  infer_instance

/-- The actual Laurent cone inclusion followed by the original inverse signed successor shift. -/
def bottomStep (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientAmbientBassDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ))).obj
        ((laurentUnderFunctor R).obj a) ⟶
      (boundedFlatCoefficientAmbientBassDiagram P (i + 1) ⋙
        stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).obj a :=
  (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion (StrictSquare.comparison
    ((boundedFlatCoefficientAmbientBassDiagram P i).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)))) ≫
    (modelDiagramBottomSuccessorIso (boundedFlatCoefficientSectionModelRow P) i).inv.app a

/-- Each original quotient keeps the actual cone inclusion and inverse signed shift. -/
@[reassoc]
theorem laurentQuotient_comparison (i : ℕ) (a : Under R) :
    laurentQuotient P i a ≫
      (boundedFlatCoefficientAmbientNegativeKComparison P (i + 1)).hom.app a =
    (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫ bottomStep P i a := by
  unfold laurentQuotient bottomStep
  rw [Category.assoc, boundedFlatCoefficientAmbientNegativeKComparison_π,
    boundedFlatCoefficientAmbientBassBottomContractionIso_π]

/-- Two unchanged quotient arrows from the double-Laurent coefficient ring. -/
def doubleLaurentQuotient (a : Under R) :
    (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor 0).obj
        ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ⟶
      (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor 2).obj a :=
  laurentQuotient P 0 ((laurentUnderFunctor R).obj a) ≫ laurentQuotient P 1 a

instance doubleLaurentQuotient_epi (a : Under R) : Epi (doubleLaurentQuotient P a) := by
  dsimp only [doubleLaurentQuotient]
  infer_instance

/-- The original second negative class map is completely determined by these representatives. -/
theorem doubleLaurentQuotient_hom_ext (a : Under R) {A : AddCommGrpCat.{u + 1}}
    {f g : (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor 2).obj a ⟶ A}
    (h : doubleLaurentQuotient P a ≫ f = doubleLaurentQuotient P a ≫ g) : f = g :=
  (cancel_epi (doubleLaurentQuotient P a)).mp h

private theorem two_step_comparison {C : Type*} [Category C]
    {A B D E F G : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : A ⟶ F) (e : F ⟶ G) (g : B ⟶ G) (h : G ⟶ E)
    (h₁ : a ≫ g = d ≫ e) (h₂ : b ≫ c = g ≫ h) :
    (a ≫ b) ≫ c = d ≫ e ≫ h := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

/-- The double representative has exactly the two original inclusions and signed inverse shifts. -/
@[reassoc]
theorem doubleLaurentQuotient_comparison (a : Under R) :
    doubleLaurentQuotient P a ≫
      (boundedFlatCoefficientAmbientNegativeKComparison P 2).hom.app a =
    (boundedFlatCoefficientAmbientNegativeKComparison P 0).hom.app
        ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ≫
      bottomStep P 0 ((laurentUnderFunctor R).obj a) ≫ bottomStep P 1 a := by
  exact two_step_comparison _ _ _ _ _ _ _
    (laurentQuotient_comparison P 0 ((laurentUnderFunctor R).obj a))
    (laurentQuotient_comparison P 1 a)

end Quillen.PerfectComplexes.CoefficientNegativeRepresentatives
