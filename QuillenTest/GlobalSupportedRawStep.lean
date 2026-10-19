/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawRows

/-! Regression clients for the actual supported split tracks, cone null and Laurent seed. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSupportedRawBass
universe u
namespace QuillenTest.GlobalSupportedRawStep

/-- The full positive normalized boundary, not just its endpoint maps, is recovered. -/
theorem positive_normalized_boundary (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (plusComparison A).at 0 = plusNormalizedHomotopy A :=
  Homotopy.RelHomotopy.at_zero _

/-- The full inverse-chart split boundary survives at every native time. -/
theorem inverse_split_boundary (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (minusComparison A).at 1 = minusHomotopy A :=
  Homotopy.RelHomotopy.at_one _

/-- The chosen null starts at the actual Laurent projection into its actual cone. -/
theorem source_null_start (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
    (x : (rawSpectrum A.obj).space n) :
    (sourceNull A).level n (0, x) =
      (mappingConeInclusion (comparison A)).map n
        ((rawMap (Geometry.laurentProjection A)).map n x) :=
  (sourceNull A).at_zero n x

/-- The same chosen null ends at the original cone point. -/
theorem source_null_finish (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
    (x : (rawSpectrum A.obj).space n) :
    (sourceNull A).level n (1, x) = (mappingCone (comparison A)).point n :=
  (sourceNull A).at_one n x

/-- The first half is exactly the original positive split track in the actual cone. -/
theorem source_null_positive_half (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
    (s : unitInterval) (x : (rawSpectrum A.obj).space n) (hs : (s : ℝ) ≤ 1 / 2) :
    (sourceNull A).level n (s, x) =
      (mappingConeInclusion (comparison A)).map n
        ((plusHomotopy A).level n
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x)) := by
  rw [sourceNull_apply, dite_eq_left hs]

/-- The independent second half is the original cone-null evaluated on its positive leg. -/
theorem source_null_cone_half (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
    (s : unitInterval) (x : (rawSpectrum A.obj).space n) (hs : ¬ (s : ℝ) ≤ 1 / 2) :
    (sourceNull A).level n (s, x) =
      (mappingConeHomotopy (comparison A)).level n
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩, (sourceLeg A).map n x) := by
  rw [sourceNull_apply, dite_eq_right hs]

/-- The actual forward Laurent coordinate keeps its original complex component after inclusion. -/
theorem laurent_scalar_component (A : Scheme.QuasiCompactOpenPairs.{u})
    (K : (boundedFlatPerfectSupported A.obj.obj.hom).FullSubcategory) :
    let r := GlobalSchemeLaurentTrack.laurentScalar (Opposite.op A.obj.obj.right)
    (boundedFlatPerfectSupported (Geometry.laurent A).obj.hom).ι.map
        ((pullbackUnitIso (Geometry.laurentProjection A) r).hom.app K) =
      (complexGlobalUnitIso (Geometry.laurent A).obj.right r).hom.app
        ((boundedFlatPerfectSupportedPullback (Geometry.laurentProjection A)).obj K).obj :=
  pullbackUnitIso_hom_original _ _ _

/-- Polynomial closure of the target row has its actual supported raw seed. -/
def polynomialTargetSeed {U X : Scheme.{u}} (j : U ⟶ X) [CompactSpace U] (T : X.Opens) :
    rawSpectrum (Scheme.Bass.pairPolynomialFunctor.obj (Rows.target j T)).obj ⟶
      step (Scheme.Bass.pairPolynomialFunctor.obj (Rows.target j T)) :=
  transition _

/-- Nested Laurent/polynomial source charts retain the complete native relative comparison. -/
def nestedSourceTriangle {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [CompactSpace X] (T : X.Opens) :
    let A := Scheme.Bass.pairLaurentFunctor.obj
      (Scheme.Bass.pairPolynomialFunctor.obj (Rows.source j T))
    (plusNormalizedHomotopy A).RelHomotopy (plusHomotopy A) :=
  plusComparison _

end QuillenTest.GlobalSupportedRawStep
