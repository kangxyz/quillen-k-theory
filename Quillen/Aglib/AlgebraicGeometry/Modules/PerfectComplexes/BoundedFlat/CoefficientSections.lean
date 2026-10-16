/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pseudofunctor
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianSections
public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckSectionEquivalence
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianSectionTransition

/-!
# Actual bounded-flat sections over joint scheme and coefficient indices

The original geometric pseudofunctor gives actual cocartesian sections, literal coefficient reindexing, original identity-evaluation equivalences and their genuine transition isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

/-- The original bounded-flat pullback pseudofunctor on the actual joint native family. -/
def boundedFlatCoefficientPseudofunctor (R : CommRingCat.{u}) :
    Pseudofunctor (LocallyDiscrete (Index R)) Cat :=
  (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).toPseudofunctor.comp
    boundedFlatPerfectPseudofunctor

/-- The actual total category retains every original geometric fiber and transition. -/
abbrev BoundedFlatCoefficientTotal (R : CommRingCat.{u}) :=
  Pseudofunctor.Grothendieck (boundedFlatCoefficientPseudofunctor R)

/-- The original joint scheme and coefficient projection. -/
def boundedFlatCoefficientProjection (R : CommRingCat.{u}) :
    BoundedFlatCoefficientTotal R ⥤ Index R :=
  Pseudofunctor.Grothendieck.forget (boundedFlatCoefficientPseudofunctor R)

variable {R : CommRingCat.{u}}

/-- Each original pseudofunctor fiber is the actual bounded-flat perfect category. -/
theorem boundedFlatCoefficientPseudofunctor_obj (i : Index R) :
    (boundedFlatCoefficientPseudofunctor R).obj ⟨i⟩ = Cat.of (BoundedFlatPerfect (space i)) := rfl

/-- Both original index coordinates act by the same original geometric pullback functor. -/
theorem boundedFlatCoefficientPseudofunctor_map {i k : Index R} (f : i ⟶ k) :
    ((boundedFlatCoefficientPseudofunctor R).map f.toLoc).toFunctor =
      boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) := rfl

/-- Actual cocartesian sections over the coslice of one joint index. -/
abbrev BoundedFlatCoefficientSections (i : Index R) :=
  underCocartesian (boundedFlatCoefficientProjection R) i

/-- Original scheme and coefficient change is literal coslice restriction. -/
def boundedFlatCoefficientSectionsMap {i k : Index R} (f : i ⟶ k) :
    BoundedFlatCoefficientSections i ⥤ BoundedFlatCoefficientSections k :=
  underCocartesianReindex (boundedFlatCoefficientProjection R) f

/-- The same original section categories and reindexings form a strict diagram. -/
def boundedFlatCoefficientSectionsFunctor (R : CommRingCat.{u}) : Index R ⥤ Cat where
  obj i := Cat.of (BoundedFlatCoefficientSections i)
  map f := (boundedFlatCoefficientSectionsMap f).toCatHom
  map_id i := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_id (boundedFlatCoefficientProjection R) i
  map_comp f g := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_comp (boundedFlatCoefficientProjection R) f g

/-- Actual identity evaluation into the specified original geometric fiber. -/
def boundedFlatCoefficientOriginalEvaluation (i : Index R) :
    BoundedFlatCoefficientSections i ⥤ BoundedFlatPerfect (space i) :=
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedFlatCoefficientPseudofunctor R) i

instance boundedFlatCoefficientOriginalEvaluation_isEquivalence (i : Index R) :
    (boundedFlatCoefficientOriginalEvaluation i).IsEquivalence :=
  inferInstanceAs (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedFlatCoefficientPseudofunctor R) i).IsEquivalence

/-- Original identity evaluation is the actual forward equivalence. -/
def boundedFlatCoefficientSectionEquivalence (i : Index R) :
    BoundedFlatCoefficientSections i ≌ BoundedFlatPerfect (space i) :=
  (boundedFlatCoefficientOriginalEvaluation i).asEquivalence

/-- The actual cocartesian transition compares evaluation with the original joint pullback. -/
def boundedFlatCoefficientSectionReindexIso {i k : Index R} (f : i ⟶ k) :
    boundedFlatCoefficientSectionsMap f ⋙ boundedFlatCoefficientOriginalEvaluation k ≅
      boundedFlatCoefficientOriginalEvaluation i ⋙
        boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) := by
  unfold boundedFlatCoefficientOriginalEvaluation
  exact eqToIso (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation_reindex
    (boundedFlatCoefficientPseudofunctor R) i f) ≪≫
    (Quillen.CategoryTheory.GrothendieckSections.originalEvaluationTransitionIso
      (boundedFlatCoefficientPseudofunctor R) i (Under.mk f)).symm

end Quillen.PerfectComplexes

end

end
