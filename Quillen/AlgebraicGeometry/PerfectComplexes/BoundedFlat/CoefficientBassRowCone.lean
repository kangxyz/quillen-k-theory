/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRowComparison
public import Quillen.Waldhausen.SConstruction.Iterated.RowMappingCone

/-!
# Genuine row interchange on the original bounded-flat Bass cone

The exact pullback maps and the prescribed reversed-positive/inverse comparison track
supply the full quotient square. The resulting row involution acts on the original Bass
cone, with its original tip and unchanged cone and overlap heights. Its double-structure
law and the complete positive source-null equation retain every original clock.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRowCone

/-- The exact model map underlying the unchanged canonically normalized raw pullback. -/
def pullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelOf (boundedFlatPerfectWaldhausen Y) ⟶ modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatPerfectPullback_exact f).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual polynomial projection model map, retaining its original zero normalization. -/
abbrev projection := pullbackModel (polynomialProjection P a)

/-- The genuine row transpose on the original two-polynomial overlap quotient. -/
abbrev spanRowSwap (k : ℕ) :=
  RowHomotopyPushout.rowSwap (projection P a) (projection P a) k

/-- The specified full Bass comparison commutes with the genuine row transpose. -/
theorem comparison_rowSwap (k : ℕ)
    (x : (RowHomotopyPushout.spectrum (projection P a) (projection P a)).space (k + 3)) :
    RowHomotopyPushout.vertex k
      (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))))
      ((boundedFlatCoefficientBassSquareComparison P a).map (k + 3) x) =
    (boundedFlatCoefficientBassSquareComparison P a).map (k + 3) (spanRowSwap P a k x) :=
  RowMappingCone.comparison_rowSwap (projection P a) (projection P a)
    (pullbackModel (laurentPlus P a)) (pullbackModel (laurentMinus P a))
    (boundedFlatCoefficientBassSquareHomotopy P a) k
    (boundedFlatCoefficientBassSquareHomotopy_rowSwap P a k) x

/-- The actual based transpose on the original Bass mapping cone, with no comparison premise. -/
def rowSwap (k : ℕ) :
    C((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space (k + 3),
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space (k + 3)) :=
  RowMappingCone.rowSwap (projection P a) (projection P a)
    (boundedFlatCoefficientBassSquareComparison P a) k (comparison_rowSwap P a k)

/-- The entire original Laurent inclusion retains its actual row transpose. -/
theorem rowSwap_inclusion (k : ℕ)
    (y : stageSpace (k + 2)
      (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))))) :
    rowSwap P a k
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 3) y) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 3)
      (stageRowSwapHomeomorph k
        (modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a)))) y)
        := rfl

/-- The entire original cone cylinder keeps its literal height. -/
theorem rowSwap_cylinder (k : ℕ) (h : unitInterval)
    (x : (RowHomotopyPushout.spectrum (projection P a) (projection P a)).space (k + 3)) :
    rowSwap P a k
      ((mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level (k + 3)
        (h, x)) =
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level (k + 3)
      (h, spanRowSwap P a k x) := rfl

/-- The prescribed cone point and tip are fixed. -/
theorem rowSwap_point (k : ℕ) :
    rowSwap P a k ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).point (k + 3)) =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).point (k + 3) :=
  RowMappingCone.rowSwap_point _ _ _ k _

/-- The actual original cone row transpose is involutive on every point. -/
theorem rowSwap_involutive (k : ℕ) : Function.Involutive (rowSwap P a k) :=
  RowMappingCone.rowSwap_involutive _ _ _ k _

/-- Two successive original structure times interchange in the unchanged cone. -/
theorem structure_rowSwap (k : ℕ)
    (x : (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space (k + 1))
    (s t : unitInterval) :
    rowSwap P a k
      ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap (k + 2)
        ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap (k + 1)
          x s) t) =
    (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap (k + 2)
      ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap (k + 1)
        x t) s :=
  RowMappingCone.structure_rowSwap _ _ _ k _ x s t

/-- The positive source leg is a whole original row-equivariant map. -/
theorem sourceLeg_rowSwap (k : ℕ)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    spanRowSwap P a k ((boundedFlatCoefficientBassSourceLeg P a).map (k + 3) x) =
    (boundedFlatCoefficientBassSourceLeg P a).map (k + 3)
      (stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x) :=
  congrArg (HomotopyPushout.left _ _ (k + 3))
    (boundedFlatPerfectPrespectrumMap_rowSwap (polynomialProjection P a) k x)

/-- Both original halves of the positive source null preserve the entire row square. -/
theorem sourceNull_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    rowSwap P a k ((boundedFlatCoefficientBassLaurentNullHomotopy P a).level (k + 3) (t, x)) =
      (boundedFlatCoefficientBassLaurentNullHomotopy P a).level (k + 3)
        (t, stageRowSwapHomeomorph k
          (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x) := by
  let H := (boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
  let K := (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).precomp
    (boundedFlatCoefficientBassSourceLeg P a)
  change rowSwap P a k
    (((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3))) (t, x)) =
      ((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3)))
        (t, stageRowSwapHomeomorph k
          (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact congrArg ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map
      (k + 3)) (boundedFlatCoefficientLaurentPlusHomotopy_rowSwap P a k _ x)
  · exact congrArg (fun y =>
      (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level (k + 3) (_, y))
      (sourceLeg_rowSwap P a k x)

end Quillen.PerfectComplexes.CoefficientBassRowCone
