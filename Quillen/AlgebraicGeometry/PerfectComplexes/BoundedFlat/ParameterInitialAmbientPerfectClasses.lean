/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialModelClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassKZeroComparison

/-! # Original ambient perfect classes at the unchanged current initial stage

The original coefficient evaluation and perfect inclusion identify nonnegative
perfect classes with the same fine section spectrum. Degree zero is the original
ambient bottom map used by the negative recursion. The parameter class law retains
the actual coefficient restriction and ambient telescope inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- Original perfect K-groups compute the unchanged fine coefficient section spectrum. -/
def boundedFlatCoefficientSectionPerfectKStableEquiv {R : CommRingCat.{u}} (i : Index R)
    [CompactSpace i.1.unop.left] (n : ℕ) :
    Additive ((perfectWaldhausen (space i)).K n) ≃+
      stableHomotopyGroup (prespectrum (boundedFlatCoefficientSectionModel i)) (n : ℤ) :=
  (boundedFlatCoefficientSectionPerfectKEquiv i n).symm.toAdditive.trans
    (modelKStableEquiv (boundedFlatCoefficientSectionModel i) n)

/-- Evaluation keeps every original fine section model representative. -/
theorem boundedFlatCoefficientSectionPerfectKStableEquiv_evaluation
    {R : CommRingCat.{u}} (i : Index R) [CompactSpace i.1.unop.left] (n : ℕ)
    (x : (boundedFlatCoefficientSectionModel i).waldhausen.K n) :
    boundedFlatCoefficientSectionPerfectKStableEquiv i n
        (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv i n x)) =
      modelKStableEquiv (boundedFlatCoefficientSectionModel i) n (Additive.ofMul x) := by
  change modelKStableEquiv (boundedFlatCoefficientSectionModel i) n (Additive.ofMul
    ((boundedFlatCoefficientSectionPerfectKEquiv i n).symm
      (boundedFlatCoefficientSectionPerfectKEquiv i n x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Degree zero is the actual original ambient comparison used by the negative recursion. -/
theorem boundedFlatCoefficientSectionPerfectKStableEquiv_zero
    {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)
    (x : (perfectWaldhausen (space (op P, a))).K 0) :
    boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) 0 (Additive.ofMul x) =
      ((boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a) (Additive.ofMul x) := by
  let : IsIso ((stableHomotopyFunctor 0).map
      (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a))) :=
    boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_isStableEquivalence (op P, a) 0
  obtain ⟨y, rfl⟩ := (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) 0).surjective x
  rw [boundedFlatCoefficientSectionPerfectKStableEquiv_evaluation]
  apply (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor 0).map
    (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)))).injective
  have he := boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv (op P, a) 0 y
  have hz := ConcreteCategory.congr_hom
    (boundedFlatCoefficientAmbientBassBottomZeroNatIso_evaluation P a)
    (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) 0 y))
  exact he.symm.trans hz.symm

namespace ParameterFullCurrentNull
open GlobalSectionChangeIndex ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.KTheory.Bass Quillen.KTheory.Bass.SchemeNaturalSeed
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]

/-- Ambient perfect classes retain the actual parameter restriction and old initial inclusion. -/
theorem current_fine_ambient_perfectClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterModels.ambient P.left).obj (specUnder.obj a)).waldhausen.K n) :
    (currentFineOpenComparison (𝟙 P) a (n : ℤ)).hom
        (currentModelClass (ParameterModels.ambient P.left) (ambientTrack P.left)
          (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a)
        (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) n
          (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) n
            (Quillen.Waldhausen.KMap ((parameterCoefficientRestriction P).app a).exact n x)))) := by
  rw [boundedFlatCoefficientSectionPerfectKStableEquiv_evaluation]
  exact current_fine_open_modelClass (𝟙 P) a n x

/-- The ambient initial zero class is the unchanged original negative-recursion bottom class. -/
theorem current_fine_ambient_originalZeroClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ParameterModels.ambient P.left).obj (specUnder.obj a)).waldhausen.K 0) :
    (currentFineOpenComparison (𝟙 P) a 0).hom
        (currentModelClass (ParameterModels.ambient P.left) (ambientTrack P.left)
          (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a)
        (((boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a)
          (Additive.ofMul (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) 0
            (Quillen.Waldhausen.KMap ((parameterCoefficientRestriction P).app a).exact 0 x)))) := by
  rw [← boundedFlatCoefficientSectionPerfectKStableEquiv_zero]
  exact current_fine_ambient_perfectClass P a 0 x

end ParameterFullCurrentNull
end Quillen.PerfectComplexes
