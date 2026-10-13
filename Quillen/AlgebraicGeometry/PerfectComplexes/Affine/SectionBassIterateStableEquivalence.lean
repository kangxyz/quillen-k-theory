/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassFunctorStableEquivalence
public import Quillen.KTheory.Bass.StrictDiagramIteration

/-!
# Stable preservation through every actual finite Bass iterate

Exact functor iteration identities identify the transformed source and target with the original
later finite section stages. The proved one-step excision theorem then applies at every step.
The conclusion uses the existing iterate functor's map of the SAME original transformation;
no replacement transformation, freshly chosen unit, or stability of the Bass seed is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Applying the actual Bass functor to an original stage gives its original successor. -/
theorem boundedFlatAffineSectionBassDiagram_bass_obj (i : ℕ) :
    KTheory.Bass.strictRingDiagramFunctor.obj (boundedFlatAffineSectionBassDiagram.{u} i) =
      boundedFlatAffineSectionBassDiagram (i + 1) := by
  change (KTheory.Bass.strictDiagramFunctor PolynomialBaseChange.laurentSquareFunctor).obj
      ((KTheory.Bass.strictDiagramIterate PolynomialBaseChange.laurentSquareFunctor i).obj
        boundedFlatAffineSectionPrespectrumFunctor) =
    (KTheory.Bass.strictDiagramIterate PolynomialBaseChange.laurentSquareFunctor (i + 1)).obj
      boundedFlatAffineSectionPrespectrumFunctor
  rw [KTheory.Bass.strictDiagramIterate_succ_right]
  rfl

/-- Applying an original iterate gives exactly the original stage with the sum index. -/
theorem boundedFlatAffineSectionBassDiagram_iterate_obj (n i : ℕ) :
    (KTheory.Bass.strictRingDiagramIterate n).obj (boundedFlatAffineSectionBassDiagram.{u} i) =
      boundedFlatAffineSectionBassDiagram (i + n) := by
  change (KTheory.Bass.strictDiagramIterate PolynomialBaseChange.laurentSquareFunctor n).obj
      ((KTheory.Bass.strictDiagramIterate PolynomialBaseChange.laurentSquareFunctor i).obj
        boundedFlatAffineSectionPrespectrumFunctor) =
    (KTheory.Bass.strictDiagramIterate PolynomialBaseChange.laurentSquareFunctor (i + n)).obj
      boundedFlatAffineSectionPrespectrumFunctor
  rw [KTheory.Bass.strictDiagramIterate_add]
  rfl

private theorem functorMap_stable_of_eq (i j : ℕ)
    (F G : CommRingCat.{u} ⥤ Quillen.LoopPrespectrum.{u + 1})
    (hF : F = boundedFlatAffineSectionBassDiagram i)
    (hG : G = boundedFlatAffineSectionBassDiagram j)
    (η : F ⟶ G) (hη : ∀ R, IsStableEquivalence (η.app R)) (R : CommRingCat.{u}) :
    IsStableEquivalence ((KTheory.Bass.strictRingDiagramFunctor.map η).app R) := by
  cases hF
  cases hG
  exact boundedFlatAffineSectionBass_functorMap_isStableEquivalence i j η hη R

private theorem iterateMap_stable_of_eq (n i j : ℕ)
    (F G : CommRingCat.{u} ⥤ Quillen.LoopPrespectrum.{u + 1})
    (hF : F = boundedFlatAffineSectionBassDiagram i)
    (hG : G = boundedFlatAffineSectionBassDiagram j)
    (η : F ⟶ G) (hη : ∀ R, IsStableEquivalence (η.app R)) (R : CommRingCat.{u}) :
    IsStableEquivalence (((KTheory.Bass.strictRingDiagramIterate n).map η).app R) := by
  induction n generalizing i j F G with
  | zero => exact hη R
  | succ n ih =>
    apply ih (i + 1) (j + 1)
      (KTheory.Bass.strictRingDiagramFunctor.obj F)
      (KTheory.Bass.strictRingDiagramFunctor.obj G)
      (hF ▸ boundedFlatAffineSectionBassDiagram_bass_obj i)
      (hG ▸ boundedFlatAffineSectionBassDiagram_bass_obj j)
      (KTheory.Bass.strictRingDiagramFunctor.map η)
    exact fun R ↦ functorMap_stable_of_eq i j F G hF hG η hη R

/-- Every actual iterate preserves the same objectwise stable finite-stage transformation. -/
theorem boundedFlatAffineSectionBass_iterateMap_isStableEquivalence (n i j : ℕ)
    (η : boundedFlatAffineSectionBassDiagram.{u} i ⟶ boundedFlatAffineSectionBassDiagram j)
    (hη : ∀ R, IsStableEquivalence (η.app R)) (R : CommRingCat.{u}) :
    IsStableEquivalence (((KTheory.Bass.strictRingDiagramIterate n).map η).app R) :=
  iterateMap_stable_of_eq n i j _ _ rfl rfl η hη R

end Quillen.PerfectComplexes
