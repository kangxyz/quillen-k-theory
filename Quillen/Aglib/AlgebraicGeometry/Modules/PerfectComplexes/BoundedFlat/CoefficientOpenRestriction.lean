/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PairPullback
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Basic

/-!
# Actual restriction on joint coefficient sections

The original scheme-over-base open map gives the specified native open pair, coefficient square, actual section restriction and original evaluation comparison.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- The specified native open pair at the actual coefficient algebra. -/
def boundedFlatCoefficientOpenPair (a : Under R) : AlgebraicGeometry.Scheme.OpenPairs.{u} :=
  ⟨Arrow.mk (schemeMap f a), (show IsOpenImmersion (schemeMap f a) from inferInstance)⟩

omit [IsOpenImmersion f.left] in
/-- Original coefficient maps commute with the actual native open inclusion. -/
theorem boundedFlatCoefficientOpenSquare {a b : Under R} (g : a ⟶ b) :
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g) ≫ schemeMap f a =
      schemeMap f b ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
        (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g) := by
  change AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op P, a)) (k := (op P, b)) (𝟙
    (op P), g) ≫
      AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, a)) (k := (op P, a)) (f.op,
        𝟙 a) =
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, b)) (k := (op P, b)) (f.op, 𝟙
      b) ≫
      AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op
        Q), g)
  rw [← AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_comp,
    ← AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_comp]
  congr 1

/-- The genuine coefficient square between the same native open pairs. -/
def boundedFlatCoefficientOpenPairMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientOpenPair f b ⟶ boundedFlatCoefficientOpenPair f a :=
  ObjectProperty.homMk (Arrow.homMk
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op P, a)) (k := (op P, b)) (𝟙 (op
      P), g))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op
      Q), g))
    (boundedFlatCoefficientOpenSquare f g))

/-- The actual restriction is the joint coslice reindexing, with its unchanged functor. -/
def boundedFlatCoefficientOpenRestriction (a : Under R) :
    BoundedFlatCoefficientSections (op Q, a) ⥤ BoundedFlatCoefficientSections (op P, a) :=
  boundedFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)

/-- Original native evaluation compares restriction with the actual geometric pullback. -/
def boundedFlatCoefficientOpenRestrictionEvaluationIso (a : Under R) :
    boundedFlatCoefficientOpenRestriction f a ⋙
        boundedFlatCoefficientOriginalEvaluation (op P, a) ≅
      boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙
        boundedFlatPerfectPullback (schemeMap f a) :=
  boundedFlatCoefficientSectionReindexIso (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)

end Quillen.PerfectComplexes

end

end
