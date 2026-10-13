/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatStableKZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumNaturality

/-!
# Original bottom-group functors of strict Bass stages

Each actual strict finite-stage diagram gives its bottom signed stable-group functor. At stage
zero the original evaluation homotopies and inclusion K-zero comparison give a natural
isomorphism from the unchanged original perfect K-zero functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The bottom signed groups retain the original strict diagram's literal coefficient maps. -/
def boundedFlatAffineSectionBassBottomFunctor (i : ℕ) :
    CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  boundedFlatAffineSectionBassDiagram i ⋙ stableHomotopyFunctor (-(i : ℤ))

/-- Original perfect K-zero identifies the actual strict section stage-zero stable group. -/
def boundedFlatAffineSectionBassBottomZeroIso (R : CommRingCat.{u}) :
    Quillen.Bass.affineKZeroFunctor.obj R ≅
      (boundedFlatAffineSectionBassBottomFunctor 0).obj R := by
  let := boundedFlatAffineSectionEvaluation_isStableEquivalence R 0
  exact boundedFlatAffineStableKZeroIso R ≪≫
    (asIso ((stableHomotopyFunctor 0).map
      (boundedFlatAffineSectionEvaluationPrespectrumMap R))).symm

/-- The stage-zero comparison retains the original evaluation map in its forward square. -/
@[reassoc]
theorem boundedFlatAffineSectionBassBottomZeroIso_evaluation (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassBottomZeroIso R).hom ≫
      (stableHomotopyFunctor 0).map (boundedFlatAffineSectionEvaluationPrespectrumMap R) =
    (boundedFlatAffineStableKZeroIso R).hom := by
  let := boundedFlatAffineSectionEvaluation_isStableEquivalence R 0
  simp [boundedFlatAffineSectionBassBottomZeroIso]

/-- Original evaluation homotopies prove coefficient naturality of the stage-zero comparison. -/
@[reassoc]
theorem boundedFlatAffineSectionBassBottomZeroIso_naturality {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    Quillen.Bass.affineKZeroFunctor.map f ≫ (boundedFlatAffineSectionBassBottomZeroIso S).hom =
      (boundedFlatAffineSectionBassBottomZeroIso R).hom ≫
        (boundedFlatAffineSectionBassBottomFunctor 0).map f := by
  let := boundedFlatAffineSectionEvaluation_isStableEquivalence S 0
  apply (cancel_mono ((stableHomotopyFunctor 0).map
    (boundedFlatAffineSectionEvaluationPrespectrumMap S))).mp
  have he := (boundedFlatAffineSectionEvaluationCoefficientHomotopy f).stableHomotopyMap_eq 0
  simp only [Functor.map_comp] at he
  change (Quillen.Bass.affineKZeroFunctor.map f ≫
      (boundedFlatAffineSectionBassBottomZeroIso S).hom) ≫ _ =
    ((boundedFlatAffineSectionBassBottomZeroIso R).hom ≫
      (stableHomotopyFunctor 0).map (boundedFlatAffineSectionPrespectrumFunctor.map f)) ≫ _
  rw [Category.assoc, boundedFlatAffineSectionBassBottomZeroIso_evaluation,
    Category.assoc, he, ← Category.assoc,
    boundedFlatAffineSectionBassBottomZeroIso_evaluation,
    boundedFlatAffineStableKZeroIso_naturality]

/-- The original perfect K-zero functor is naturally the actual strict stage-zero bottom functor.
-/
def boundedFlatAffineSectionBassBottomZeroNatIso :
    Quillen.Bass.affineKZeroFunctor.{u} ≅ boundedFlatAffineSectionBassBottomFunctor 0 :=
  NatIso.ofComponents boundedFlatAffineSectionBassBottomZeroIso
    (fun f => boundedFlatAffineSectionBassBottomZeroIso_naturality f)

end Quillen.PerfectComplexes
