/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientCone
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitBassComposite
public import Quillen.Topology.Prespectrum.NullLoopNaturality

/-!
# The genuine coefficient-cell composite with the original Bass cofiber

Use the independently realized first coefficient cell, the unchanged raw Bass cofiber inclusion,
and precisely the tensor-unitor extension of the original positive source null. The whole
null/unit/null word gives an actual map into parameter loops of the ordinary loop-tail cone.
Its equality to the actual tensor Bass transition followed by the actual stabilization is proved
as an equality of prespectrum maps. The original scalar seed is related by a whole homotopy.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The genuine coefficient cell followed by the unchanged Bass cofiber inclusion. -/
def boundedFlatCoefficientCellConeTrack :=
  tensorUnitPullbackCoefficientConeHomotopy (laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- The whole cell/cofiber track equals the stabilized image of the same original tensor track.
-/
theorem boundedFlatCoefficientCellConeTrack_eq :
    boundedFlatCoefficientCellConeTrack P a =
      (boundedFlatCoefficientTensorConeTrack P a).postcomp
        (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  tensorUnitPullbackCoefficientConeHomotopy_eq _ _ _

/-- Keep the original tensor unitor and positive null, postcomposed by actual stabilization. -/
def boundedFlatCoefficientCellConeNull :=
  ((boundedFlatCoefficientTensorConeNull P a).postcomp
    (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))).cast
      (g' := zeroHom
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))))
        (looping (tail (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))))
      rfl (by
        apply Quillen.LoopPrespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        exact (stabilizationMap
          (mappingCone (boundedFlatCoefficientBassSquareComparison P a))).map_point n)

/-- The independently realized first coefficient cell gives a genuine whole stabilized map. -/
def boundedFlatCoefficientCellBassTransition :
    originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      parameterLooping (looping (tail
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  (boundedFlatCoefficientCellConeTrack P a).nullLoopMap
    (boundedFlatCoefficientCellConeNull P a)

/-- Strict equality of whole maps, retaining the original null word and both loop directions. -/
theorem boundedFlatCoefficientCellBassTransition_eq :
    boundedFlatCoefficientCellBassTransition P a =
      boundedFlatCoefficientTensorBassTransition P a ≫
        parameterLoopingMap
          (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))))
    (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))
    (boundedFlatCoefficientTensorConeTrack P a) (boundedFlatCoefficientCellConeTrack P a)
    (boundedFlatCoefficientTensorConeNull P a) (boundedFlatCoefficientCellConeNull P a)
    (fun n => by rw [boundedFlatCoefficientCellConeTrack_eq]; rfl) (fun _ => rfl)
  exact h.symm

/-- Whole comparison to the unchanged forward scalar seed after the same actual stable map. -/
def boundedFlatCoefficientCellBassTransitionHomotopy :
    Homotopy (boundedFlatCoefficientCellBassTransition P a)
      (boundedFlatCoefficientBassTransition P a ≫ parameterLoopingMap
        (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  ((boundedFlatCoefficientTensorBassTransitionHomotopy P a).postcomp
    (parameterLoopingMap
      (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a))))).cast
        (boundedFlatCoefficientCellBassTransition_eq P a).symm rfl

/-- The actual word has independent unit/null-loop time and coefficient-row time. -/
theorem boundedFlatCoefficientCellBassTransition_apply (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t s : unitInterval) :
    Path.toContinuousMap
        (Path.toContinuousMap ((boundedFlatCoefficientCellBassTransition P a).map n x) t) s =
      Path.toContinuousMap
        (((boundedFlatCoefficientCellConeTrack P a).conjugateToZero
          (boundedFlatCoefficientCellConeNull P a)).level n (t, x)) s := rfl

/-- The exact whole word, including every original concatenation clock, is stabilized literally.
-/
theorem boundedFlatCoefficientCellBassTransition_word (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t s : unitInterval) :
    Path.toContinuousMap
        (Path.toContinuousMap ((boundedFlatCoefficientCellBassTransition P a).map n x) t) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap n
        (((boundedFlatCoefficientTensorConeTrack P a).conjugateToZero
          (boundedFlatCoefficientTensorConeNull P a)).level n (t, x)) s := by
  rw [boundedFlatCoefficientCellBassTransition_eq]
  rfl

end Quillen.PerfectComplexes
