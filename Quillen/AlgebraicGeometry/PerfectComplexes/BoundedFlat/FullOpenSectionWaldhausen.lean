/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenZero
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckZeroSections
public import Quillen.Waldhausen.EquivalenceStructure

/-!
# Full-open section evaluation and its inherited chosen zero

The original identity evaluation is the genuine Grothendieck section equivalence. The zero
family is the image of the original coarse section zero under the specified restriction.
Its single global section reindexes literally. Transport through original evaluation supplies
the full-open Waldhausen structure with that same chosen zero and the original geometric classes.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckZeroSections Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original identity evaluation into the specified full-open fiber category. -/
def boundedFlatAffineFullOpenOriginalEvaluation (a : Under R) :
    BoundedFlatAffineFullOpenSections j a ⥤ BoundedFlatPerfect (openSpace j a) :=
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedFlatAffineFullOpenPseudofunctor j) a

instance instIsEquivalenceBoundedFlatAffineFullOpenOriginalEvaluation (a : Under R) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).IsEquivalence :=
  inferInstanceAs (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedFlatAffineFullOpenPseudofunctor j) a).IsEquivalence

/-- The original evaluation functor is the actual forward equivalence. -/
def boundedFlatAffineFullOpenSectionEquivalence (a : Under R) :
    BoundedFlatAffineFullOpenSections j a ≌ BoundedFlatPerfect (openSpace j a) :=
  (boundedFlatAffineFullOpenOriginalEvaluation j a).asEquivalence

/-- Actual open pullback preserves the specified original image-zero universal property. -/
theorem boundedFlatAffineFullOpenImageZero_map_isZero {a b : Under R} (f : a ⟶ b) :
    IsZero (((boundedFlatAffineFullOpenPseudofunctor j).map f.toLoc).toFunctor.obj
      (boundedFlatAffineSectionFullOpenImageZero j a)) :=
  (boundedFlatPerfectPullback (openMap j f)).map_isZero
    (isZero_boundedFlatAffineSectionFullOpenImageZero j a)

/-- A single actual global image-zero family supplies the chosen zero in every coefficient fiber. -/
def boundedFlatAffineFullOpenSectionZero (a : Under R) :
    BoundedFlatAffineFullOpenSections j a :=
  sectionZero (boundedFlatAffineFullOpenPseudofunctor j)
    (boundedFlatAffineSectionFullOpenImageZero j)
    (isZero_boundedFlatAffineSectionFullOpenImageZero j)
    (fun {_ _} f => boundedFlatAffineFullOpenImageZero_map_isZero j f) a

/-- Original evaluation retains the inherited image zero literally. -/
theorem boundedFlatAffineFullOpenOriginalEvaluation_sectionZero (a : Under R) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).obj
        (boundedFlatAffineFullOpenSectionZero j a) =
      boundedFlatAffineSectionFullOpenImageZero j a := rfl

/-- The original coefficient reindexing retains the same global chosen-zero section. -/
theorem boundedFlatAffineFullOpenSectionsMap_sectionZero {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionsMap j f).obj
        (boundedFlatAffineFullOpenSectionZero j a) =
      boundedFlatAffineFullOpenSectionZero j b :=
  reindex_sectionZero (boundedFlatAffineFullOpenPseudofunctor j)
    (boundedFlatAffineSectionFullOpenImageZero j)
    (isZero_boundedFlatAffineSectionFullOpenImageZero j)
    (fun {_ _} g => boundedFlatAffineFullOpenImageZero_map_isZero j g) f

/-- Actual full-open morphism classes and pushouts, with the inherited original image zero. -/
def boundedFlatAffineFullOpenSectionWaldhausen (a : Under R) :
    Waldhausen.Structure (BoundedFlatAffineFullOpenSections j a) :=
  (boundedFlatPerfectWaldhausen (openSpace j a)).ofEquivalence
    (boundedFlatAffineFullOpenSectionEquivalence j a)
    (boundedFlatAffineFullOpenSectionZero j a)
    (isZero_boundedFlatAffineSectionFullOpenImageZero j a)

/-- The unchanged identity evaluation is exact for the actual full-open structures. -/
theorem boundedFlatAffineFullOpenOriginalEvaluation_exact (a : Under R) :
    Waldhausen.IsExact (boundedFlatAffineFullOpenSectionWaldhausen j a).cof
      (boundedFlatAffineFullOpenSectionWaldhausen j a).weq
      (boundedFlatPerfectWaldhausen (openSpace j a)).cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineFullOpenOriginalEvaluation j a) :=
  Waldhausen.Structure.ofEquivalence_exact _ _ _ _

end Quillen.PerfectComplexes
