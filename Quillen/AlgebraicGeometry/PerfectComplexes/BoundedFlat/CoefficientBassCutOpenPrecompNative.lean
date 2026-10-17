/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

/-! Full carrier precomposition recovers original native input precomposition at every level. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenPrecomp
open CutOpenCarrier
variable {U V W T : Model.{u}} (A : U ⟶ V) (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.functor ≅ (F ≫ J).functor)

/-- The complete nerve family, beyond vertices, preserves the genuine precomposed input. -/
theorem pointwise_precomp (n : ℕ) (y : |parameterSSet F|) (x : (prespectrum U).space n) :
    pointwisePrespectrumFamily (A ≫ F) n (parameterMap A F y) x =
      pointwisePrespectrumFamily F n y ((prespectrumMap A).map n x) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  have h := mapParameter_parameter (precompNode A) N z
  change pointwisePrespectrumFamily (A ≫ F) n (mapParameter (precompNode A) _) x = _
  rw [h, pointwisePrespectrumFamily_parameter, pointwisePrespectrumFamily_parameter]
  exact prespectrumFamily_precomp N A n z x

/-- Both original sheets, both tips and the whole Laurent summand have the exact native image. -/
theorem map_native (n : ℕ) (y : space F J G ε₀ ε₁) (x : (prespectrum U).space n) :
    nativeEval (A ≫ F) J (A ≫ G) (anchor A F J G ε₀) (anchor A F J G ε₁) n
      (map A F J G ε₀ ε₁ y) x =
    nativeEval F J G ε₀ ε₁ n y ((prespectrumMap A).map n x) := by
  rcases exists_native_cell F J G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, t, rfl⟩ | ⟨z, t, rfl⟩ | rfl | rfl
  · rw [map_laurent, nativeEval_laurentInclusion, nativeEval_laurentInclusion,
      pointwise_precomp]
  · rw [map_cylinderMinus, nativeEval_cylinderMinus, nativeEval_cylinderMinus,
      pointwise_precomp]
  · rw [map_cylinderPlus, nativeEval_cylinderPlus, nativeEval_cylinderPlus,
      pointwise_precomp]
  · rw [map_tipMinus, nativeEval_tipMinus, nativeEval_tipMinus]
  · rw [map_tipPlus, nativeEval_tipPlus, nativeEval_tipPlus]

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenPrecomp
