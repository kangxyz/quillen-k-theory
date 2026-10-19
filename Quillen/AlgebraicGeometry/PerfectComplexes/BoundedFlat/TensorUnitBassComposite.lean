/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitHomotopy
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationBassSeed
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# The actual tensor-unit track after the original raw Bass cone inclusion

Use the unchanged raw bounded-flat coefficient Bass comparison and its original positive source
null. The genuine tensor unitor extends that same null to the actual tensor-pullback endpoint.
Its proved whole iterated-S pasting compares the resulting tensor/null word to the original
forward scalar/null word, and currying gives a homotopy into the same parameter-correct cone loop.

This is a whole raw spectrum-track comparison. Identifying the independently constructed fixed
first-coefficient cell action with this track after realization remains a separate consumer;
this file does not infer such an identification from the coefficient K-one class alone. It also
does not replace the comparison from the strict global-section diagram by a change of names.
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

/-- The genuine tensor action of the same original forward coefficient Laurent unit. -/
def boundedFlatCoefficientTensorUnitHomotopy :=
  boundedFlatPerfectTensorUnitHomotopy (laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))

/-- The original tensor unitor followed by the unchanged raw Bass cone inclusion. -/
def boundedFlatCoefficientTensorConeMovement :=
  (boundedFlatPerfectTensorUnitUnitorHomotopy (laurentProjection P a)).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- The actual tensor coefficient track followed by the same raw cofiber inclusion. -/
def boundedFlatCoefficientTensorConeTrack :=
  (boundedFlatCoefficientTensorUnitHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- Extend the original positive source null only by the genuine displayed tensor unitor. -/
def boundedFlatCoefficientTensorConeNull :=
  (boundedFlatCoefficientTensorConeMovement P a).trans
    (boundedFlatCoefficientBassLaurentNullHomotopy P a)

/-- The whole actual tensor-unit square retains every original time after cone inclusion. -/
def boundedFlatCoefficientTensorConePasting :
    ((boundedFlatCoefficientTensorConeTrack P a).trans
      (boundedFlatCoefficientTensorConeMovement P a)).RelHomotopy
      ((boundedFlatCoefficientTensorConeMovement P a).trans
        ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))) := by
  simpa only [Homotopy.postcomp_trans, boundedFlatCoefficientTensorConeTrack,
    boundedFlatCoefficientTensorConeMovement, boundedFlatCoefficientTensorUnitHomotopy,
    boundedFlatCoefficientLaurentUnitHomotopy] using
    (boundedFlatPerfectTensorUnitUnitorPasting (laurentProjection P a)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- Cancel only the proved tensor unitor inside the two whole original null/unit/null words. -/
def boundedFlatCoefficientTensorConeWordComparison :
    ((boundedFlatCoefficientTensorConeTrack P a).conjugateToZero
      (boundedFlatCoefficientTensorConeNull P a)).RelHomotopy
      (((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).conjugateToZero
          (boundedFlatCoefficientBassLaurentNullHomotopy P a)) :=
  Homotopy.RelHomotopy.conjugateNaturality (boundedFlatCoefficientTensorConeMovement P a)
    (boundedFlatCoefficientTensorConeTrack P a)
    ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))
    (boundedFlatCoefficientTensorConeNull P a) (boundedFlatCoefficientBassLaurentNullHomotopy P a)
    (boundedFlatCoefficientTensorConePasting P a) (Homotopy.RelHomotopy.refl _)

/-- The actual tensor/null construction lands in parameter-correct loops of the same raw cone. -/
def boundedFlatCoefficientTensorBassTransition :
    originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      boundedFlatCoefficientBassStep P a :=
  (boundedFlatCoefficientTensorConeTrack P a).nullLoopMap
    (boundedFlatCoefficientTensorConeNull P a)

/-- The entire raw tensor/null transition is homotopic to the original raw forward Bass seed. -/
def boundedFlatCoefficientTensorBassTransitionHomotopy :
    Homotopy (boundedFlatCoefficientTensorBassTransition P a)
      (boundedFlatCoefficientBassTransition P a) :=
  (boundedFlatCoefficientTensorConeWordComparison P a).zeroLoopMapHomotopy

/-- Both independent original loop and relative-comparison times are retained literally. -/
theorem boundedFlatCoefficientTensorBassTransitionHomotopy_apply (n : ℕ)
    (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
        ((boundedFlatCoefficientTensorBassTransitionHomotopy P a).level n (r, x)) s =
      (boundedFlatCoefficientTensorConeWordComparison P a).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
