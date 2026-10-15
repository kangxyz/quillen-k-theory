/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficitGrading
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenImagePullback
public import Quillen.Waldhausen.Cofinality.ComplementMap

/-!
# The original image quotient grading on global native open sections

Original identity evaluation and bounded-flat inclusion pull the actual
raw-perfect image quotient grading back to the native open section row.
Pointwise grading and change of weakness require only the original open arrow.
The restriction image has zero grade by its actual geometric image witness.

Compactness of the original ambient scheme and open propagates to their native
coefficient fibers and supplies the existing derived action on the same raw
quotients. That action proves graded reindexing exact. The joint zero section
and strict joint reindexing laws then construct the actual graded Model and
prespectrum diagrams, with a coefficient-natural change of weakness. No
flatness, affine-scheme, regularity or noetherian hypothesis is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.AlgebraicGrothendieck
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- The unchanged raw-perfect image quotient for the actual native open inclusion. -/
abbrev BoundedFlatCoefficientOpenImageQuotient (a : Under R) :=
  ImageQuotient (perfectOpenWeakWaldhausen (schemeMap f a))
    (perfectRestrict (schemeMap f a)) (perfectOpenRestrict_waldhausenExact (schemeMap f a))

/-- Native open identity evaluation followed by the original bounded-flat perfect inclusion. -/
def boundedFlatCoefficientFullOpenPerfectEvaluation (_f : P ⟶ Q) (a : Under R) :
    BoundedFlatCoefficientSections (op P, a) ⥤ Perfect (space (op P, a)) :=
  boundedFlatCoefficientOriginalEvaluation (op P, a) ⋙
    boundedFlatPerfectInclusion (space (op P, a))

omit [IsOpenImmersion f.left] in
/-- The displayed original perfect evaluation is genuinely exact. -/
theorem boundedFlatCoefficientFullOpenPerfectEvaluation_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSectionWaldhausen (op P, a)).cof
      (boundedFlatCoefficientSectionWaldhausen (op P, a)).weq
      (perfectWaldhausen (space (op P, a))).cof
      (perfectWaldhausen (space (op P, a))).weq
      (boundedFlatCoefficientFullOpenPerfectEvaluation f a) :=
  (boundedFlatCoefficientOriginalEvaluation_exact (op P, a)).comp
    (boundedFlatPerfectInclusion_exact (space (op P, a)))

/-- Actual section grades in the unchanged original geometric image quotient. -/
def boundedFlatCoefficientFullOpenGrading (a : Under R) :
    Cofinality.Grading (boundedFlatCoefficientSectionWaldhausen (op P, a))
      (BoundedFlatCoefficientOpenImageQuotient f a) :=
  (perfectOpenDeficitGrading (schemeMap f a)).comap
    (boundedFlatCoefficientFullOpenPerfectEvaluation_exact f a)

/-- Every section grade is precisely its original perfect evaluation's quotient class. -/
theorem boundedFlatCoefficientFullOpenGrading_value (a : Under R)
    (S : BoundedFlatCoefficientSections (op P, a)) :
    (boundedFlatCoefficientFullOpenGrading f a).value S =
      (perfectOpenDeficitGrading (schemeMap f a)).value
        ((boundedFlatCoefficientFullOpenPerfectEvaluation f a).obj S) := rfl

/-- Grade weakness retains the one original joint zero literally. -/
theorem boundedFlatCoefficientFullOpenGrading_zero (a : Under R) :
    (boundedFlatCoefficientFullOpenGrading f a).coarseStructure.zero =
      boundedFlatCoefficientSectionZero (op P, a) := rfl

/-- The universal algebraic extension is the same raw quotient after actual perfect evaluation. -/
theorem boundedFlatCoefficientFullOpenGrading_lift (a : Under R) :
    lift (boundedFlatCoefficientSectionWaldhausen (op P, a))
        (boundedFlatCoefficientFullOpenGrading f a) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap f a))
          (perfectRestrict (schemeMap f a))
          (perfectOpenRestrict_waldhausenExact (schemeMap f a))).range).comp
        (AlgebraicGrothendieck.map (boundedFlatCoefficientSectionWaldhausen (op P, a))
          (boundedFlatCoefficientFullOpenPerfectEvaluation f a)
          (boundedFlatCoefficientFullOpenPerfectEvaluation_exact f a)) := by
  apply hom_ext (boundedFlatCoefficientSectionWaldhausen (op P, a))
  intro S
  rw [lift_objectClass, AddMonoidHom.comp_apply, map_objectClass]
  rfl

/-- The actual restricted section has zero grade by its original geometric image witness. -/
theorem boundedFlatCoefficientOpenRestriction_grade_zero (a : Under R)
    (S : BoundedFlatCoefficientSections (op Q, a)) :
    (boundedFlatCoefficientFullOpenGrading f a).value
      ((boundedFlatCoefficientOpenRestriction f a).obj S) = 0 := by
  change (perfectOpenDeficitGrading (schemeMap f a)).value
    ((boundedFlatPerfectInclusion (space (op P, a))).obj
      ((boundedFlatCoefficientOriginalEvaluation (op P, a)).obj
        ((boundedFlatCoefficientOpenRestriction f a).obj S))) = 0
  apply imageQuotientGrading_zero_of_weakImage
  let e := (boundedFlatPerfectOriginalRestrictionIso (schemeMap f a)).app
    ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S) ≪≫
    ((boundedFlatPerfectInclusion (space (op P, a))).mapIso
      ((boundedFlatCoefficientOpenRestrictionEvaluationIso f a).app S)).symm
  refine ⟨(boundedFlatPerfectInclusion (space (op Q, a))).obj
    ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S), e.hom, ?_⟩
  exact (perfectWaldhausen (space (op P, a))).weq_iso e.hom
    (show IsIso e.hom from inferInstance)

/-- The actual graded Model keeps the native section category, cofibrations and joint zero. -/
def boundedFlatCoefficientGradedOpenModel (a : Under R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatCoefficientSections (op P, a)),
    (boundedFlatCoefficientFullOpenGrading f a).coarseStructure⟩

/-- The identity on native sections changes only the actual original weakness class. -/
def boundedFlatCoefficientOpenGradingModelMap (a : Under R) :
    (boundedFlatCoefficientFullOpenModelFunctor f).obj a ⟶
      boundedFlatCoefficientGradedOpenModel f a where
  functor := 𝟭 (BoundedFlatCoefficientSections (op P, a))
  exact := Fibration.changeWeak_exact (boundedFlatCoefficientFullOpenGrading f a).nested
  zero := rfl

variable [CompactSpace P.left] [CompactSpace Q.left]

local instance coefficientOpenCompact (a : Under R) : CompactSpace (space (op P, a)) :=
  compactSpace_space (op P, a)

local instance coefficientAmbientCompact (a : Under R) : CompactSpace (space (op Q, a)) :=
  compactSpace_space (op Q, a)

/-- Arbitrary coefficient maps act on the unchanged actual raw-perfect image quotients. -/
def boundedFlatCoefficientOpenImageMap {a b : Under R} (g : a ⟶ b) :
    BoundedFlatCoefficientOpenImageQuotient f a →+
      BoundedFlatCoefficientOpenImageQuotient f b :=
  perfectOpenImageQuotientPullback (schemeMap f a) (schemeMap f b)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g)

/-- The quotient action computes exactly the grade of every original reindexed section. -/
theorem boundedFlatCoefficientOpenImageMap_value {a b : Under R} (g : a ⟶ b)
    (S : BoundedFlatCoefficientSections (op P, a)) :
    boundedFlatCoefficientOpenImageMap f g ((boundedFlatCoefficientFullOpenGrading f a).value S) =
      (boundedFlatCoefficientFullOpenGrading f b).value
        ((boundedFlatCoefficientSectionsMap
          (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).obj S) := by
  change perfectOpenImageQuotientPullback (schemeMap f a) (schemeMap f b)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g)
      ((imageQuotientGrading (perfectOpenWeakWaldhausen (schemeMap f a))
        (perfectRestrict (schemeMap f a))
        (perfectOpenRestrict_waldhausenExact (schemeMap f a))).value
          ((boundedFlatPerfectInclusion (space (op P, a))).obj
          ((boundedFlatCoefficientOriginalEvaluation (op P, a)).obj S))) = _
  rw [perfectOpenImageQuotientPullback_boundedFlat_objectClass]
  let e := (boundedFlatPerfectInclusion (space (op P, b))).mapIso
    ((boundedFlatCoefficientSectionReindexIso
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).app S)
  exact (perfectOpenDeficitGrading (schemeMap f b)).weak e.inv
    ((perfectWaldhausen (space (op P, b))).weq_iso e.inv
      (show IsIso e.inv from inferInstance))

/-- Original coefficient reindexing is exact for actual grade-equality weakness. -/
theorem boundedFlatCoefficientGradedOpenSectionsMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedFlatCoefficientFullOpenGrading f a).coarseStructure.cof
      (boundedFlatCoefficientFullOpenGrading f a).coarseStructure.weq
      (boundedFlatCoefficientFullOpenGrading f b).coarseStructure.cof
      (boundedFlatCoefficientFullOpenGrading f b).coarseStructure.weq
      (boundedFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)) where
  zero := (boundedFlatCoefficientSectionsMap_exact
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).zero
  cofibration := (boundedFlatCoefficientSectionsMap_exact
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).cofibration
  weak {S T} _ h :=
    (boundedFlatCoefficientOpenImageMap_value f g S).symm.trans
      ((congrArg (boundedFlatCoefficientOpenImageMap f g) h).trans
        (boundedFlatCoefficientOpenImageMap_value f g T))
  pushout := (boundedFlatCoefficientSectionsMap_exact
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)).pushout

/-- The same graded coefficient map retains the one joint global zero literally. -/
def boundedFlatCoefficientGradedOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientGradedOpenModel f a ⟶ boundedFlatCoefficientGradedOpenModel f b where
  functor := boundedFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
  exact := boundedFlatCoefficientGradedOpenSectionsMap_exact f g
  zero := boundedFlatCoefficientSectionsMap_sectionZero
    (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)

/-- The actual graded coefficient Model diagram has the same strict reindexing laws. -/
def boundedFlatCoefficientGradedOpenModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientGradedOpenModel f
  map := boundedFlatCoefficientGradedOpenModelMap f
  map_id a := by
    apply Model.Hom.ext
    exact underCocartesianReindex_id (boundedFlatCoefficientProjection R) (op P, a)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact underCocartesianReindex_comp (boundedFlatCoefficientProjection R)
      (X := (op P, a)) (Y := (op P, b)) (Z := (op P, c))
      (𝟙 (op P), g) (𝟙 (op P), h)

/-- The original fine-to-graded changes of weakness commute with every coefficient arrow. -/
def boundedFlatCoefficientOpenGradingModelTransformation :
    boundedFlatCoefficientFullOpenModelFunctor f ⟶
      boundedFlatCoefficientGradedOpenModelFunctor f where
  app := boundedFlatCoefficientOpenGradingModelMap f
  naturality a b g := by
    apply Model.Hom.ext
    change boundedFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b))
      (𝟙 (op P), g) ⋙ 𝟭 _ = 𝟭 _ ⋙
        boundedFlatCoefficientSectionsMap (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
    simp only [Functor.comp_id, Functor.id_comp]

/-- Original iterated-S realization of the same actual graded global coefficient Models. -/
def boundedFlatCoefficientGradedOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientGradedOpenModelFunctor f ⋙ prespectrumFunctor

/-- The unchanged Model change of weakness gives the actual global grading prespectrum map. -/
def boundedFlatCoefficientOpenGradingPrespectrumTransformation :
    boundedFlatCoefficientFullOpenPrespectrumFunctor f ⟶
      boundedFlatCoefficientGradedOpenPrespectrumFunctor f :=
  Functor.whiskerRight (boundedFlatCoefficientOpenGradingModelTransformation f) prespectrumFunctor

end Quillen.PerfectComplexes
