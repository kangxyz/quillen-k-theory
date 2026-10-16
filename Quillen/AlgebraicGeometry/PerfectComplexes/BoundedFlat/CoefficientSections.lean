/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSections


public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pseudofunctor
public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckZeroSections
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianSectionTransition
public import Quillen.Waldhausen.EquivalenceStructure
public import Quillen.Waldhausen.ExtensionCategory.ExactTransport
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-!
# Original bounded-flat Models on the joint coefficient index

The actual joint scheme and coefficient family is composed with the original
bounded-flat geometric pseudofunctor. Its cocartesian coslice sections reindex
strictly, and original identity evaluation is an actual fiber equivalence.
One pointwise chosen-zero family gives one global zero section for both index
coordinates. Each section Waldhausen structure transports the original fiber
classes and retains the corresponding restriction of that same zero section.

The actual evaluation transition and exact geometric pullback prove reindexing
exact, while the global zero section proves literal zero preservation. Thus the
same original reindexing functors form a strict fine Model diagram. Native open
rows use these Models directly; comparisons with prior pair-specific chosen
zeros are separate maps. No compactness, relative weak class, Laurent seed or
completed-spectrum assertion is supplied here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckZeroSections
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

variable {R : CommRingCat.{u}}

/-- The source-independent actual bounded-flat zero in every joint fiber. -/
def boundedFlatCoefficientChosenZero (i : Index R) :
    (boundedFlatCoefficientPseudofunctor R).obj ⟨i⟩ :=
  (boundedFlatPerfectWaldhausen (space i)).zero

/-- The original chosen fiber zero keeps its actual universal property. -/
theorem boundedFlatCoefficientChosenZero_isZero (i : Index R) :
    IsZero (boundedFlatCoefficientChosenZero i) :=
  (boundedFlatPerfectWaldhausen (space i)).isZero

/-- Actual geometric pullback preserves the original fiber zero's universal property. -/
theorem boundedFlatCoefficientChosenZero_map_isZero {i k : Index R} (f : i ⟶ k) :
    IsZero (((boundedFlatCoefficientPseudofunctor R).map f.toLoc).toFunctor.obj
      (boundedFlatCoefficientChosenZero i)) :=
  (boundedFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).map_isZero
    (boundedFlatPerfectWaldhausen (space i)).isZero

/-- One actual zero section on the entire joint index, independent of an initial row. -/
def boundedFlatCoefficientGlobalZeroSection (R : CommRingCat.{u}) :
    Index R ⥤ BoundedFlatCoefficientTotal R :=
  globalSection (boundedFlatCoefficientPseudofunctor R) boundedFlatCoefficientChosenZero
    boundedFlatCoefficientChosenZero_isZero

/-- The one global zero section retains the actual joint projection literally. -/
theorem boundedFlatCoefficientGlobalZeroSection_comp (R : CommRingCat.{u}) :
    boundedFlatCoefficientGlobalZeroSection R ⋙ boundedFlatCoefficientProjection R =
      𝟭 (Index R) := rfl

/-- Every coslice zero is the restriction of the one actual joint zero section. -/
def boundedFlatCoefficientSectionZero (i : Index R) : BoundedFlatCoefficientSections i :=
  sectionZero (boundedFlatCoefficientPseudofunctor R) boundedFlatCoefficientChosenZero
    boundedFlatCoefficientChosenZero_isZero
    (fun {_ _} f => boundedFlatCoefficientChosenZero_map_isZero f) i

/-- The restricted joint zero section is genuinely a zero object. -/
theorem isZero_boundedFlatCoefficientSectionZero (i : Index R) :
    IsZero (boundedFlatCoefficientSectionZero i) :=
  isZero_sectionZero (boundedFlatCoefficientPseudofunctor R) boundedFlatCoefficientChosenZero
    boundedFlatCoefficientChosenZero_isZero
    (fun {_ _} f => boundedFlatCoefficientChosenZero_map_isZero f) i

/-- Original identity evaluation retains precisely the original bounded-flat fiber zero. -/
theorem boundedFlatCoefficientOriginalEvaluation_sectionZero (i : Index R) :
    (boundedFlatCoefficientOriginalEvaluation i).obj (boundedFlatCoefficientSectionZero i) =
      (boundedFlatPerfectWaldhausen (space i)).zero :=
  originalEvaluation_sectionZero (boundedFlatCoefficientPseudofunctor R)
    boundedFlatCoefficientChosenZero boundedFlatCoefficientChosenZero_isZero
    (fun {_ _} f => boundedFlatCoefficientChosenZero_map_isZero f) i

/-- Every original joint reindexing retains the very same global zero section literally. -/
theorem boundedFlatCoefficientSectionsMap_sectionZero {i k : Index R} (f : i ⟶ k) :
    (boundedFlatCoefficientSectionsMap f).obj (boundedFlatCoefficientSectionZero i) =
      boundedFlatCoefficientSectionZero k :=
  reindex_sectionZero (boundedFlatCoefficientPseudofunctor R) boundedFlatCoefficientChosenZero
    boundedFlatCoefficientChosenZero_isZero
    (fun {_ _} g => boundedFlatCoefficientChosenZero_map_isZero g) f

/-- The original fiber Waldhausen classes and pushouts, with the same actual joint zero. -/
def boundedFlatCoefficientSectionWaldhausen (i : Index R) :
    Waldhausen.Structure (BoundedFlatCoefficientSections i) :=
  (boundedFlatPerfectWaldhausen (space i)).ofEquivalence
    (boundedFlatCoefficientSectionEquivalence i) (boundedFlatCoefficientSectionZero i) (by
      change IsZero ((boundedFlatCoefficientOriginalEvaluation i).obj
        (boundedFlatCoefficientSectionZero i))
      rw [boundedFlatCoefficientOriginalEvaluation_sectionZero]
      exact (boundedFlatPerfectWaldhausen (space i)).isZero)

/-- The original chosen Waldhausen zero is the same restricted joint zero section. -/
theorem boundedFlatCoefficientSectionWaldhausen_zero (i : Index R) :
    (boundedFlatCoefficientSectionWaldhausen i).zero = boundedFlatCoefficientSectionZero i := rfl

/-- Cofibrations are exactly those of the original identity-evaluated fiber map. -/
theorem boundedFlatCoefficientSectionWaldhausen_cof_iff (i : Index R)
    {S T : BoundedFlatCoefficientSections i} (f : S ⟶ T) :
    (boundedFlatCoefficientSectionWaldhausen i).cof f ↔
      (boundedFlatPerfectWaldhausen (space i)).cof
        ((boundedFlatCoefficientOriginalEvaluation i).map f) := Iff.rfl

/-- Weak equivalences are exactly those of the original identity-evaluated fiber map. -/
theorem boundedFlatCoefficientSectionWaldhausen_weq_iff (i : Index R)
    {S T : BoundedFlatCoefficientSections i} (f : S ⟶ T) :
    (boundedFlatCoefficientSectionWaldhausen i).weq f ↔
      (boundedFlatPerfectWaldhausen (space i)).weq
        ((boundedFlatCoefficientOriginalEvaluation i).map f) := Iff.rfl

/-- Original identity evaluation is exact for these transported original classes. -/
theorem boundedFlatCoefficientOriginalEvaluation_exact (i : Index R) :
    Waldhausen.IsExact (boundedFlatCoefficientSectionWaldhausen i).cof
      (boundedFlatCoefficientSectionWaldhausen i).weq
      (boundedFlatPerfectWaldhausen (space i)).cof (boundedFlatPerfectWaldhausen (space i)).weq
      (boundedFlatCoefficientOriginalEvaluation i) :=
  Waldhausen.Structure.ofEquivalence_exact _ _ _ _

/-- The actual inverse evaluation equivalence is exact for the same original structures. -/
theorem boundedFlatCoefficientSectionEquivalence_inverse_exact (i : Index R) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen (space i)).cof
      (boundedFlatPerfectWaldhausen (space i)).weq
      (boundedFlatCoefficientSectionWaldhausen i).cof
      (boundedFlatCoefficientSectionWaldhausen i).weq
      (boundedFlatCoefficientSectionEquivalence i).inverse :=
  Waldhausen.Structure.ofEquivalence_inverse_exact _ _ _ _

/-- Reindexing followed by actual fiber evaluation is exact. -/
theorem boundedFlatCoefficientSectionsMap_evaluation_exact {i k : Index R} (f : i ⟶ k) :
    Waldhausen.IsExact (boundedFlatCoefficientSectionWaldhausen i).cof
      (boundedFlatCoefficientSectionWaldhausen i).weq
      (boundedFlatPerfectWaldhausen (space k)).cof (boundedFlatPerfectWaldhausen (space k)).weq
      (boundedFlatCoefficientSectionsMap f ⋙ boundedFlatCoefficientOriginalEvaluation k) :=
  Waldhausen.ExtensionCategory.isExact_of_natIso
    (boundedFlatCoefficientSectionWaldhausen i) (boundedFlatPerfectWaldhausen (space k))
    ((boundedFlatCoefficientOriginalEvaluation_exact i).comp
      (boundedFlatPerfectPullback_exact (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)))
    (boundedFlatCoefficientSectionReindexIso f).symm

/-- Original joint reindexing preserves zero, cofibrations, weak maps and pushouts. -/
theorem boundedFlatCoefficientSectionsMap_exact {i k : Index R} (f : i ⟶ k) :
    Waldhausen.IsExact (boundedFlatCoefficientSectionWaldhausen i).cof
      (boundedFlatCoefficientSectionWaldhausen i).weq
      (boundedFlatCoefficientSectionWaldhausen k).cof
      (boundedFlatCoefficientSectionWaldhausen k).weq
      (boundedFlatCoefficientSectionsMap f) where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedFlatCoefficientOriginalEvaluation k) _
    ((boundedFlatCoefficientSectionsMap_evaluation_exact f).zero hx)
  cofibration g hg := (boundedFlatCoefficientSectionsMap_evaluation_exact f).cofibration g hg
  weak g hg := (boundedFlatCoefficientSectionsMap_evaluation_exact f).weak g hg
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedFlatCoefficientOriginalEvaluation k)
    exact (boundedFlatCoefficientSectionsMap_evaluation_exact f).pushout hi hp

/-- The fine section Model retains the original native fiber structure and joint zero. -/
def boundedFlatCoefficientSectionModel (i : Index R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatCoefficientSections i), boundedFlatCoefficientSectionWaldhausen i⟩

/-- The original exact reindexing is literally zero-preserving in the actual Model category. -/
def boundedFlatCoefficientSectionModelMap {i k : Index R} (f : i ⟶ k) :
    boundedFlatCoefficientSectionModel i ⟶ boundedFlatCoefficientSectionModel k where
  functor := boundedFlatCoefficientSectionsMap f
  exact := boundedFlatCoefficientSectionsMap_exact f
  zero := boundedFlatCoefficientSectionsMap_sectionZero f

/-- All original scheme and coefficient maps form one actual strict fine Model diagram. -/
def boundedFlatCoefficientSectionModelFunctor (R : CommRingCat.{u}) : Index R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSectionModel
  map := boundedFlatCoefficientSectionModelMap
  map_id i := by
    apply Model.Hom.ext
    exact underCocartesianReindex_id (boundedFlatCoefficientProjection R) i
  map_comp f g := by
    apply Model.Hom.ext
    exact underCocartesianReindex_comp (boundedFlatCoefficientProjection R) f g

/-- Apply the original iterated-S realization to the same actual fine Models. -/
def boundedFlatCoefficientSectionPrespectrumFunctor (R : CommRingCat.{u}) :
    Index R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSectionModelFunctor R ⋙ prespectrumFunctor

/-- The native coefficient Model row of a specified scheme over the unchanged base. -/
def boundedFlatCoefficientSectionModelRow (P : Over (Spec R)) : Under R ⥤ Model.{u+1} :=
  row P ⋙ boundedFlatCoefficientSectionModelFunctor R

/-- Native scheme restriction uses the same joint zero-preserving Model reindexing. -/
def boundedFlatCoefficientSectionModelRestriction {P Q : Over (Spec R)} (f : P ⟶ Q) :
    boundedFlatCoefficientSectionModelRow Q ⟶ boundedFlatCoefficientSectionModelRow P :=
  Functor.whiskerRight (rowTransformation f) (boundedFlatCoefficientSectionModelFunctor R)

/-- Every native restriction component is the unchanged original joint Model map. -/
theorem boundedFlatCoefficientSectionModelRestriction_app {P Q : Over (Spec R)}
    (f : P ⟶ Q) (a : Under R) :
    (boundedFlatCoefficientSectionModelRestriction f).app a =
      boundedFlatCoefficientSectionModelMap (f.op, 𝟙 a) := rfl

end Quillen.PerfectComplexes
