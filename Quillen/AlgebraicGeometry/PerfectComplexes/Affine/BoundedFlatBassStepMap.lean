/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassSpanComparisonTrack
public import Quillen.Topology.Prespectrum.ConeHomotopySquare

/-!
# Actual coefficient maps of bounded-flat one-step Bass spectra

The proved original comparison-map homotopy supplies the cone map and its parameter-correct
looping. Composition coherence and compatibility with the seed transition remain separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The genuine comparison-map homotopy induces an actual map of the original Bass square cones. -/
def boundedFlatBassConeMap :
    mappingCone (boundedFlatBassSquareComparison R) ⟶
      mappingCone (boundedFlatBassSquareComparison S) :=
  mappingConeSquareMap _ _ (boundedFlatPolynomialSpanMap f)
    (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))
    (boundedFlatBassComparisonCoefficientHomotopy f)

/-- Parameter-correct looping gives a map between the actual one-step Bass spectra. -/
def boundedFlatAffineBassStepMap : boundedFlatAffineBassStep R ⟶ boundedFlatAffineBassStep S :=
  parameterLoopingMap (boundedFlatBassConeMap f)

/-- The literal Laurent inclusion commutes with the actual coefficient cone map. -/
lemma boundedFlatBassConeMap_inclusion :
    mappingConeInclusion (boundedFlatBassSquareComparison R) ≫ boundedFlatBassConeMap f =
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison S) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The whole cone cylinder retains the actual coefficient comparison and target cone null track. -/
lemma boundedFlatBassConeMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).space n) :
    (boundedFlatBassConeMap f).map n
      (ReducedMappingCone.cylinder _ _ ((boundedFlatBassSquareComparison R).map n) (s, x)) =
    (((boundedFlatBassComparisonCoefficientHomotopy f).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))).trans
      (Homotopy.precomp (boundedFlatPolynomialSpanMap f)
        (mappingConeHomotopy (boundedFlatBassSquareComparison S)))).level n (s, x) := rfl

end Quillen.PerfectComplexes
