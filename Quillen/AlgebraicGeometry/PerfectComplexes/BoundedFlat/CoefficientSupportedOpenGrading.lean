/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportedPerfectEvaluation


public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.ImageQuotientPullback
public import Quillen.Waldhausen.Cofinality.ComplementMap

/-!
# Actual supported native coefficient image-quotient grading

The raw quotient is the actual supported relative restriction image quotient.
Original supported evaluation and bounded-flat inclusion give its native open
section grading. Actual supported restriction has zero grade by its original
geometric image witness. The pointwise graded Model retains the supported
native category and the one joint zero, without compactness assumptions.

Compactness of the original ambient and localization schemes supplies the
proved quotient action on native coefficient squares. It gives exact graded
coefficient reindexing and genuine strict Model diagrams G_Z and q_Z. No
compactness of the auxiliary support open, separation, flatness, density, or
extension premise is imposed. No null track, cone, or cofinality theorem is
asserted here.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.AlgebraicGrothendieck
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation

/-- The actual raw supported image quotient for the same native support and localization opens. -/
abbrev BoundedFlatCoefficientSupportedOpenImageQuotient (a : Under R) :=
  PerfectSupportedOpenImageQuotient (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)

omit [IsOpenImmersion f.left] in
/-- The original supported perfect evaluation is exact for the actual fine structures. -/
theorem boundedFlatCoefficientSupportedFullOpenPerfectEvaluation_exact (a : Under R) :
    IsExact
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).weq
      (perfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι).cof
      (perfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι).weq
      (boundedFlatCoefficientSupportedFullOpenPerfectEvaluation f T a) :=
  (boundedFlatCoefficientSupportedEvaluation_exact
    (boundedFlatCoefficientOpenSupportOpen f T a).ι).comp
    (boundedFlatPerfectSupportedInclusion_exact (boundedFlatCoefficientOpenSupportOpen f T a).ι)

/-- Original supported native open sections carry their actual raw image-quotient grades. -/
def boundedFlatCoefficientSupportedFullOpenGrading (a : Under R) :
    Cofinality.Grading
      (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι)
      (BoundedFlatCoefficientSupportedOpenImageQuotient f T a) :=
  (perfectSupportedOpenDeficitGrading
    (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).comap
    (boundedFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a)

/-- Native grades retain the actual original supported perfect evaluation value. -/
theorem boundedFlatCoefficientSupportedFullOpenGrading_value (a : Under R)
    (S : BoundedFlatCoefficientSupportedOpenSections f T a) :
    (boundedFlatCoefficientSupportedFullOpenGrading f T a).value S =
      (perfectSupportedOpenDeficitGrading (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).value
        ((boundedFlatCoefficientSupportedFullOpenPerfectEvaluation f T a).obj S) := rfl

/-- The graded structure retains the restriction of the same original joint global zero. -/
theorem boundedFlatCoefficientSupportedFullOpenGrading_zero (a : Under R) :
    (boundedFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.zero =
      boundedFlatCoefficientSupportedSectionZero
        (boundedFlatCoefficientOpenSupportOpen f T a).ι := rfl

/-- The actual native algebraic grading extension is the unchanged raw quotient projection. -/
theorem boundedFlatCoefficientSupportedFullOpenGrading_lift (a : Under R) :
    lift (boundedFlatCoefficientSupportedSectionWaldhausen
        (boundedFlatCoefficientOpenSupportOpen f T a).ι)
        (boundedFlatCoefficientSupportedFullOpenGrading f T a) =
      (QuotientAddGroup.mk'
        (map (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a))
          (perfectSupportedRestrict (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a))
          (perfectSupportedOpenRestrict_waldhausenExact
            (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a))).range).comp
        (map (boundedFlatCoefficientSupportedSectionWaldhausen
          (boundedFlatCoefficientOpenSupportOpen f T a).ι)
          (boundedFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
          (boundedFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a)) := by
  apply hom_ext (boundedFlatCoefficientSupportedSectionWaldhausen
    (boundedFlatCoefficientOpenSupportOpen f T a).ι)
  intro S
  rw [lift_objectClass, AddMonoidHom.comp_apply, map_objectClass]
  rfl

/-- Actual supported native restriction has zero quotient grade by its original image witness. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_grade_zero (a : Under R)
    (S : BoundedFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    (boundedFlatCoefficientSupportedFullOpenGrading f T a).value
      ((boundedFlatCoefficientSupportedOpenRestriction f T a).obj S) = 0 := by
  change (perfectSupportedOpenDeficitGrading (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a)).value
      ((boundedFlatPerfectSupportedInclusion
        (boundedFlatCoefficientOpenSupportOpen f T a).ι).obj
        ((boundedFlatCoefficientSupportedEvaluation
          (boundedFlatCoefficientOpenSupportOpen f T a).ι).obj
          ((boundedFlatCoefficientSupportedOpenRestriction f T a).obj S))) = 0
  apply imageQuotientGrading_zero_of_weakImage
  let e := (boundedFlatPerfectSupportedOriginalRestrictionIso (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a)).app
      ((boundedFlatCoefficientSupportedEvaluation
        (boundedFlatCoefficientSupportOpen Q T a).ι).obj S)
    ≪≫ ((boundedFlatPerfectSupportedInclusion
      (boundedFlatCoefficientOpenSupportOpen f T a).ι).mapIso
      ((boundedFlatCoefficientSupportedOpenRestrictionEvaluationIso f T a).app S)).symm
  refine ⟨(boundedFlatPerfectSupportedInclusion
    (boundedFlatCoefficientSupportOpen Q T a).ι).obj
    ((boundedFlatCoefficientSupportedEvaluation (boundedFlatCoefficientSupportOpen Q T a).ι).obj S),
    e.hom, ?_⟩
  exact (perfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι).weq_iso e.hom
    (show IsIso e.hom from inferInstance)

/-- The actual graded supported native Model retains its category, cofibrations, and joint zero. -/
def boundedFlatCoefficientSupportedGradedOpenModel (a : Under R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatCoefficientSupportedOpenSections f T a),
    (boundedFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure⟩

/-- The original identity on supported native sections changes only quotient-grade weakness. -/
def boundedFlatCoefficientSupportedOpenGradingModelMap (a : Under R) :
    boundedFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedFlatCoefficientSupportedGradedOpenModel f T a where
  functor := 𝟭 (BoundedFlatCoefficientSupportedOpenSections f T a)
  exact := Fibration.changeWeak_exact (boundedFlatCoefficientSupportedFullOpenGrading f T a).nested
  zero := rfl

variable [CompactSpace P.left] [CompactSpace Q.left]

local instance coefficientSupportedOpenCompact (a : Under R) : CompactSpace (space (op P, a)) :=
  compactSpace_space (op P, a)

local instance coefficientSupportedAmbientCompact (a : Under R) : CompactSpace (space (op Q, a)) :=
  compactSpace_space (op Q, a)

/-- Arbitrary original coefficient arrows act on the actual raw supported image quotients. -/
def boundedFlatCoefficientSupportedOpenImageMap {a b : Under R} (g : a ⟶ b) :
    BoundedFlatCoefficientSupportedOpenImageQuotient f T a →+
      BoundedFlatCoefficientSupportedOpenImageQuotient f T b :=
  perfectSupportedOpenImageQuotientPullback (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a) (schemeMap f b)
    (boundedFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g).symm

/-- The proved quotient action computes every actual supported reindexed section grade. -/
theorem boundedFlatCoefficientSupportedOpenImageMap_value {a b : Under R} (g : a ⟶ b)
    (S : BoundedFlatCoefficientSupportedOpenSections f T a) :
    boundedFlatCoefficientSupportedOpenImageMap f T g
        ((boundedFlatCoefficientSupportedFullOpenGrading f T a).value S) =
      (boundedFlatCoefficientSupportedFullOpenGrading f T b).value
        ((boundedFlatCoefficientSupportedOpenMap f T g).obj S) := by
  change perfectSupportedOpenImageQuotientPullback (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a) (schemeMap f b)
    (boundedFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g).symm
      ((perfectSupportedOpenDeficitGrading (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a)).value
          ((boundedFlatPerfectSupportedInclusion
            (boundedFlatCoefficientOpenSupportOpen f T a).ι).obj
            ((boundedFlatCoefficientSupportedEvaluation
              (boundedFlatCoefficientOpenSupportOpen f T a).ι).obj S))) = _
  have h₀ := perfectSupportedOpenImageQuotientPullback_boundedFlat_objectClass
    (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) (schemeMap f b)
    (boundedFlatCoefficientSupportPairMap Q T g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g).symm
    ((boundedFlatCoefficientSupportedEvaluation
      (boundedFlatCoefficientOpenSupportOpen f T a).ι).obj S)
  let e := (boundedFlatPerfectSupportedInclusion
    (boundedFlatCoefficientOpenSupportOpen f T b).ι).mapIso
    ((boundedFlatCoefficientSupportedSectionReindexIso
      (boundedFlatCoefficientOpenSupportOpen f T a).ι
      (boundedFlatCoefficientOpenSupportOpen f T b).ι
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
      (boundedFlatCoefficientOpenSupportPairMap f T g).hom.left
      (Arrow.w (boundedFlatCoefficientOpenSupportPairMap f T g).hom)).app S)
  exact h₀.trans ((perfectSupportedOpenDeficitGrading (schemeMap f b)
    (boundedFlatCoefficientSupportOpen Q T b)).weak e.inv
    ((perfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T b).ι).weq_iso e.inv
      (show IsIso e.inv from inferInstance)))

/-- Original supported coefficient reindexing is exact for actual quotient-grade weakness. -/
theorem boundedFlatCoefficientSupportedGradedOpenSectionsMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.cof
      (boundedFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.weq
      (boundedFlatCoefficientSupportedFullOpenGrading f T b).coarseStructure.cof
      (boundedFlatCoefficientSupportedFullOpenGrading f T b).coarseStructure.weq
      (boundedFlatCoefficientSupportedOpenMap f T g) where
  zero := (boundedFlatCoefficientSupportedOpenMap_fine_exact f T g).zero
  cofibration := (boundedFlatCoefficientSupportedOpenMap_fine_exact f T g).cofibration
  weak {S V} _ h :=
    (boundedFlatCoefficientSupportedOpenImageMap_value f T g S).symm.trans
      ((congrArg (boundedFlatCoefficientSupportedOpenImageMap f T g) h).trans
        (boundedFlatCoefficientSupportedOpenImageMap_value f T g V))
  pushout := (boundedFlatCoefficientSupportedOpenMap_fine_exact f T g).pushout

/-- Actual graded coefficient reindexing retains the same supported joint zero literally. -/
def boundedFlatCoefficientSupportedGradedOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedGradedOpenModel f T a ⟶
      boundedFlatCoefficientSupportedGradedOpenModel f T b where
  functor := boundedFlatCoefficientSupportedOpenMap f T g
  exact := boundedFlatCoefficientSupportedGradedOpenSectionsMap_exact f T g
  zero := (boundedFlatCoefficientSupportedFullOpenModelMap f T g).zero

/-- The actual G_Z coefficient Model diagram retains the original strict reindexing laws. -/
def boundedFlatCoefficientSupportedGradedOpenModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSupportedGradedOpenModel f T
  map := boundedFlatCoefficientSupportedGradedOpenModelMap f T
  map_id a := by
    apply Model.Hom.ext
    exact congrArg (fun m : boundedFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedFlatCoefficientSupportedFullOpenModel f T a ↦ m.functor)
      ((boundedFlatCoefficientSupportedFullOpenModelFunctor f T).map_id a)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact congrArg (fun m : boundedFlatCoefficientSupportedFullOpenModel f T a ⟶
      boundedFlatCoefficientSupportedFullOpenModel f T c ↦ m.functor)
      ((boundedFlatCoefficientSupportedFullOpenModelFunctor f T).map_comp g h)

/-- The actual q_Z identity change of weakness is natural for every coefficient arrow. -/
def boundedFlatCoefficientSupportedOpenGradingModelTransformation :
    boundedFlatCoefficientSupportedFullOpenModelFunctor f T ⟶
      boundedFlatCoefficientSupportedGradedOpenModelFunctor f T where
  app := boundedFlatCoefficientSupportedOpenGradingModelMap f T
  naturality a b g := by
    apply Model.Hom.ext
    change boundedFlatCoefficientSupportedOpenMap f T g ⋙ 𝟭 _ =
      𝟭 _ ⋙ boundedFlatCoefficientSupportedOpenMap f T g
    simp only [Functor.comp_id, Functor.id_comp]

/-- The original iterated-S prespectra of the actual supported graded native Models. -/
def boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSupportedGradedOpenModelFunctor f T ⋙ prespectrumFunctor

/-- The same q_Z Model transformation gives the original supported grading prespectrum map. -/
def boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation :
    boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T ⟶
      boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T :=
  Functor.whiskerRight
    (boundedFlatCoefficientSupportedOpenGradingModelTransformation f T) prespectrumFunctor

end Quillen.PerfectComplexes
