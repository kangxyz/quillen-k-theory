/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedInputNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitBassComposite

/-! # The original tensor cone null on supported inputs

The composite normalization precedes the unchanged tensor-unitor/positive null.
The whole relative comparison keeps this supplied null and its original clocks.
The target is the original ambient Bass cone; no supported Bass target is introduced.
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
  {U : Scheme.{u}} (j : U ⟶ space (op P, a)) [IsOpenImmersion j]

/-- The actual supported composite tensor loop after the original raw cone inclusion. -/
def tensorSupportedInputConeTrack :=
  (tensorSupportedCompositeHomotopy j (laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (Scheme.PolynomialLaurent.laurentGlobalUnit a.right))).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- The real binary normalization moves into the separately based original tensor map. -/
def tensorSupportedInputConeMovement :=
  (tensorSupportedInputNormalization j (laurentProjection P a)).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- Precompose the supplied tensor-unitor and positive source null, at unchanged times. -/
def tensorSupportedInputOriginalNull :=
  (boundedFlatCoefficientTensorConeNull P a).precomp (tensorSupportedInputPrespectrumMap j)

/-- Prepend only the actual composite normalization to that same supplied original null. -/
def tensorSupportedInputConeNull :=
  (tensorSupportedInputConeMovement P a j).trans (tensorSupportedInputOriginalNull P a j)

/-- The entire unit/normalization square after the original cone inclusion. -/
def tensorSupportedInputConePasting :
    ((tensorSupportedInputConeTrack P a j).trans
      (tensorSupportedInputConeMovement P a j)).RelHomotopy
      ((tensorSupportedInputConeMovement P a j).trans
        ((boundedFlatCoefficientTensorConeTrack P a).precomp
          (tensorSupportedInputPrespectrumMap j))) := by
  have precomp_postcomp {D E F G : LoopPrespectrum.{u + 1}}
      {f g : E ⟶ F} (h : D ⟶ E) (H : Homotopy f g) (k : F ⟶ G) :
      (H.precomp h).postcomp k = (H.postcomp k).precomp h := by
    apply Quillen.LoopPrespectrum.Homotopy.ext
    rfl
  simpa only [tensorSupportedInputConeTrack, tensorSupportedInputConeMovement,
    Homotopy.postcomp_trans, boundedFlatCoefficientTensorConeTrack,
    boundedFlatCoefficientTensorUnitHomotopy, precomp_postcomp] using
    (tensorSupportedInputNormalizationPasting j (laurentProjection P a)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (Scheme.PolynomialLaurent.laurentGlobalUnit a.right))).postcomp
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- Whole null/unit/null comparison with the original supported input, without a new filler. -/
def tensorSupportedInputConeWordComparison :
    ((tensorSupportedInputConeTrack P a j).conjugateToZero
      (tensorSupportedInputConeNull P a j)).RelHomotopy
      (((boundedFlatCoefficientTensorConeTrack P a).precomp
        (tensorSupportedInputPrespectrumMap j)).conjugateToZero
          (tensorSupportedInputOriginalNull P a j)) :=
  Homotopy.RelHomotopy.conjugateNaturality (tensorSupportedInputConeMovement P a j)
    (tensorSupportedInputConeTrack P a j)
    ((boundedFlatCoefficientTensorConeTrack P a).precomp (tensorSupportedInputPrespectrumMap j))
    (tensorSupportedInputConeNull P a j) (tensorSupportedInputOriginalNull P a j)
    (tensorSupportedInputConePasting P a j) (Homotopy.RelHomotopy.refl _)

/-- The actual relative comparison retains both the null-loop and comparison coordinates. -/
theorem tensorSupportedInputConeWordComparison_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :
    Path.toContinuousMap
      ((tensorSupportedInputConeWordComparison P a j).zeroLoopMapHomotopy.level n (r, x)) s =
      (tensorSupportedInputConeWordComparison P a j).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
