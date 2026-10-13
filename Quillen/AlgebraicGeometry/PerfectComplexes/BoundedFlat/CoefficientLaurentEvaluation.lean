/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationUnitPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassSeed
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIntertwiningHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-!
# The original native fine-row Laurent unit across actual evaluation

The supplied native fine-row action is unchanged. Its original forward Laurent unit,
the E1 evaluation track and the original normalized raw geometric unit give a whole
relative pasting and square. Their unit, comparison, loop and structure parameters
remain independent. No Bass seed, chart-boundary, cone-null or completed comparison
is supplied by this unit square alone.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.Scheme.CoefficientBaseChange Quillen.PolynomialBaseChange
open Quillen.FunctorIdentityAutomorphism Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso

/-- The original fine native Laurent track followed by the same actual evaluation. -/
def boundedFlatCoefficientFullOpenLaurentEvaluationOldUnit (a : Under R) :=
  (boundedFlatCoefficientFullOpenLaurentHomotopy (R := R) f a).postcomp
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap
      (op P, (laurentUnderFunctor R).obj a))

/-- Original base evaluation followed by the original raw unit on the actual native joint map. -/
def boundedFlatCoefficientFullOpenLaurentEvaluationNewUnit (_f : P ⟶ Q) (a : Under R) :=
  Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatPerfectUnitHomotopy
      (Quillen.Scheme.CoefficientBaseChange.map
        (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
        (𝟙 (op P), (laurentUnderCoefficient R).app a))
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentGlobalUnit a.right)))

/-- The actual forward unit square yields the whole original native relative pasting. -/
def boundedFlatCoefficientFullOpenLaurentEvaluationUnitPasting (a : Under R) :
    ((boundedFlatCoefficientFullOpenLaurentEvaluationOldUnit f a).trans
      (boundedFlatCoefficientSectionEvaluationHomotopy
        (R := R) (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
        (𝟙 (op P), (laurentUnderCoefficient R).app a))).RelHomotopy
    ((boundedFlatCoefficientSectionEvaluationHomotopy
        (R := R) (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (laurentUnderCoefficient R).app a)).trans
        (boundedFlatCoefficientFullOpenLaurentEvaluationNewUnit f a)) := by
  let ℓ : (op P, a) ⟶ (op P, (laurentUnderFunctor R).obj a) :=
    (𝟙 (op P), (laurentUnderCoefficient R).app a)
  let r := boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
    (laurentGlobalUnit a.right)
  let J := boundedFlatCoefficientSectionEvaluationUnitPasting
    (R := R) (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a)) ℓ r
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr <;> rfl

/-- Reverse-track cancellation retains the exact original Laurent boundary. -/
def boundedFlatCoefficientFullOpenLaurentEvaluationUnitBoundary (a : Under R) :
    (boundedFlatCoefficientFullOpenLaurentEvaluationOldUnit f a).RelHomotopy
      (((boundedFlatCoefficientSectionEvaluationHomotopy
        (R := R) (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
        (𝟙 (op P), (laurentUnderCoefficient R).app a)).trans
          (boundedFlatCoefficientFullOpenLaurentEvaluationNewUnit f a)).trans
        (boundedFlatCoefficientSectionEvaluationHomotopy
        (R := R)           (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
          (𝟙 (op P), (laurentUnderCoefficient R).app a)).symm) :=
  Homotopy.RelHomotopy.conjugateBoundary _ _ _
    (boundedFlatCoefficientFullOpenLaurentEvaluationUnitPasting f a)

/-- The original fine/native raw Laurent actions have a genuine whole evaluation square. -/
def boundedFlatCoefficientFullOpenLaurentEvaluationUnitSquare (a : Under R) :
    (boundedFlatCoefficientFullOpenLaurentEvaluationOldUnit f a).Square
      (boundedFlatCoefficientFullOpenLaurentEvaluationNewUnit f a)
      (boundedFlatCoefficientSectionEvaluationHomotopy
        (R := R) (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
        (𝟙 (op P), (laurentUnderCoefficient R).app a))
      (boundedFlatCoefficientSectionEvaluationHomotopy
        (R := R) (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
        (𝟙 (op P), (laurentUnderCoefficient R).app a)) :=
  (boundedFlatCoefficientFullOpenLaurentEvaluationUnitBoundary f a).toSquare

end Quillen.PerfectComplexes
