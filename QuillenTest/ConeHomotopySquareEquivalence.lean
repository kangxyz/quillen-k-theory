/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ConeHomotopyComparison
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurent

/-! Consumers check the actual polynomial/Laurent cone comparisons, the unchanged square-track
midpoint, and cancellation of a whole arrow homotopy on the original signed stable groups. -/
@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped unitInterval
universe u
namespace QuillenTest.ConeHomotopySquareEquivalence

open Quillen

/-- The three actual affine Bass leg maps have stable original bounded-flat cone comparisons. -/
theorem polynomialLaurent_cone_comparisons (R : CommRingCat.{u}) :
    IsStableEquivalence (boundedFlatPerfectFlatPullbackConeMap (polynomialProjection R)) ∧
      IsStableEquivalence (boundedFlatPerfectFlatPullbackConeMap (laurentPlus R)) ∧
      IsStableEquivalence (boundedFlatPerfectFlatPullbackConeMap (laurentMinus R)) :=
  ⟨boundedFlatPerfectFlatPullbackConeMap_isStableEquivalence _,
    boundedFlatPerfectFlatPullbackConeMap_isStableEquivalence _,
    boundedFlatPerfectFlatPullbackConeMap_isStableEquivalence _⟩

/-- At source cylinder time one quarter, the unchanged map evaluates the supplied track at one
half, rather than replacing the track by an endpoint or constant homotopy. -/
theorem squareMap_quarter_retains_track_midpoint
    {E F E' F' : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
    (H : Homotopy (f ≫ b) (a ≫ g)) (n : ℕ) (x : E.space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
        (⟨1 / 4, by norm_num⟩, x)) =
      (mappingConeInclusion g).map n (H.level n (⟨1 / 2, by norm_num⟩, x)) := by
  have h := mappingConeSquareMap_first_half f g a b H n ⟨1 / 2, by norm_num⟩ x
  convert h using 1
  norm_num

/-- The actual reverse track cancels on every original integer-graded stable group. -/
theorem reverseTrack_stable_cancellation
    {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} (H : Homotopy f g) (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeHomotopyMap H) ≫
      (stableHomotopyFunctor d).map (mappingConeHomotopyMap H.symm) =
        𝟙 (stableHomotopyGroup (mappingCone f) d) := by
  rw [← Functor.map_comp]
  exact ((mappingConeHomotopyMapLeftHomotopy H).stableHomotopyMap_eq d).trans
    ((stableHomotopyFunctor d).map_id _)

end QuillenTest.ConeHomotopySquareEquivalence
