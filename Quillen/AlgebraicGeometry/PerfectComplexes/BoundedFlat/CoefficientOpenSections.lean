/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction
public import Quillen.Waldhausen.Fibration.InverseImageWeakEquivalence

/-!
# Global native open coefficient Models

An actual open arrow of schemes over `Spec R` gives the native ambient and open
rows of the joint section diagram. The ambient coarse structure is the inverse
image of the original relative-open weak class under original identity
evaluation. The actual section restriction is exact into the fine native open
row and preserves the one joint zero literally.

Every coefficient arrow uses the original joint reindexing. The actual native
open square proves coarse exactness, and strict section reindexing proves the
restriction square. No compactness, flatness or affine-scheme hypothesis is
needed for these Models or their prespectra.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.CoefficientBaseChange
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

/-- Fine original evaluation is exact into the actual relative-open fiber. -/
theorem boundedFlatCoefficientOpenEvaluation_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).cof
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).weq
      (boundedFlatCoefficientOriginalEvaluation (op Q, a)) :=
  (boundedFlatCoefficientOriginalEvaluation_exact (op Q, a)).changeWeakTarget
    (boundedFlatPerfectOpenNested (schemeMap f a))

/-- Original relative-open weakness on the unchanged ambient sections and joint zero. -/
def boundedFlatCoefficientOpenWaldhausen (a : Under R) :
    Structure (BoundedFlatCoefficientSections (op Q, a)) :=
  Structure.withInverseImageWeak (boundedFlatCoefficientOpenEvaluation_exact f a)

/-- The unchanged fine ambient weak class is contained in this actual coarse class. -/
def boundedFlatCoefficientOpenNested (a : Under R) :
    Fibration.NestedWeakEquivalences (boundedFlatCoefficientSectionWaldhausen (op Q, a)) :=
  Structure.inverseImageWeakNested (boundedFlatCoefficientOpenEvaluation_exact f a)

/-- Coarse original evaluation preserves precisely the original relative-open weak maps. -/
theorem boundedFlatCoefficientOpenEvaluation_coarse_exact (a : Under R) :
    IsExact (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).cof
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).weq
      (boundedFlatCoefficientOriginalEvaluation (op Q, a)) :=
  Structure.withInverseImageWeak_exact (boundedFlatCoefficientOpenEvaluation_exact f a)

/-- The actual inverse of original evaluation is exact for the same coarse structures. -/
theorem boundedFlatCoefficientOpenEquivalence_inverse_exact (a : Under R) :
    IsExact (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).cof
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).weq
      (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (boundedFlatCoefficientSectionEquivalence (op Q, a)).inverse :=
  Structure.withInverseImageWeak_inverse_exact
    (boundedFlatCoefficientSectionEquivalence (op Q, a))
    (boundedFlatCoefficientOriginalEvaluation_exact (op Q, a))
    (boundedFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))
    (boundedFlatPerfectOpenNested (schemeMap f a))

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

/-- Coarse restriction followed by native fine evaluation is genuinely exact. -/
theorem boundedFlatCoefficientOpenRestriction_evaluation_exact (a : Under R) :
    IsExact (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (boundedFlatPerfectWaldhausen (space (op P, a))).cof
      (boundedFlatPerfectWaldhausen (space (op P, a))).weq
      (boundedFlatCoefficientOpenRestriction f a ⋙
        boundedFlatCoefficientOriginalEvaluation (op P, a)) :=
  ExtensionCategory.isExact_of_natIso
    (boundedFlatCoefficientOpenWaldhausen f a) (boundedFlatPerfectWaldhausen (space (op P, a)))
    ((boundedFlatCoefficientOpenEvaluation_coarse_exact f a).comp
      (boundedFlatPerfectOpenRestriction_exact (schemeMap f a)))
    (boundedFlatCoefficientOpenRestrictionEvaluationIso f a).symm

/-- The same original restriction preserves zero, cofibrations, weak maps and pushouts. -/
theorem boundedFlatCoefficientOpenRestriction_exact (a : Under R) :
    IsExact (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (boundedFlatCoefficientSectionWaldhausen (op P, a)).cof
      (boundedFlatCoefficientSectionWaldhausen (op P, a)).weq
      (boundedFlatCoefficientOpenRestriction f a) where
  zero := (boundedFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)).zero
  cofibration := (boundedFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)).cofibration
  weak g hg := (boundedFlatCoefficientOpenRestriction_evaluation_exact f a).weak g hg
  pushout := (boundedFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)).pushout

/-- The original coefficient reindexing is exact for the coarse native ambient structures. -/
theorem boundedFlatCoefficientOpenSectionsMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (boundedFlatCoefficientOpenWaldhausen f b).cof
      (boundedFlatCoefficientOpenWaldhausen f b).weq
      (boundedFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)) where
  zero := (boundedFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).zero
  cofibration := (boundedFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).cofibration
  pushout := (boundedFlatCoefficientSectionsMap_exact
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).pushout
  weak k hk := by
    exact (ExtensionCategory.isExact_of_natIso
      (boundedFlatCoefficientOpenWaldhausen f a)
      (boundedFlatPerfectOpenWaldhausen (schemeMap f b))
      ((boundedFlatCoefficientOpenEvaluation_coarse_exact f a).comp
        (boundedFlatPerfectOpenPullback_exact (boundedFlatCoefficientOpenPairMap f g)))
      (boundedFlatCoefficientSectionReindexIso
        (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)).symm).weak k hk

/-- The actual coarse Model on native ambient sections retains the joint global zero. -/
def boundedFlatCoefficientOpenModel (a : Under R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatCoefficientSections (op Q, a)), boundedFlatCoefficientOpenWaldhausen f a⟩

/-- Every original coefficient map is exact and literally zero-preserving for this coarse Model. -/
def boundedFlatCoefficientOpenModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientOpenModel f a ⟶ boundedFlatCoefficientOpenModel f b where
  functor := boundedFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
  exact := boundedFlatCoefficientOpenSectionsMap_exact f g
  zero := boundedFlatCoefficientSectionsMap_sectionZero
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)

/-- The global coarse coefficient diagram, with strict original identity and composition. -/
def boundedFlatCoefficientOpenModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientOpenModel f
  map := boundedFlatCoefficientOpenModelMap f
  map_id a := by
    apply Model.Hom.ext
    exact underCocartesianReindex_id (boundedFlatCoefficientProjection R) (op Q, a)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact underCocartesianReindex_comp (boundedFlatCoefficientProjection R)
      (X := (op Q, a)) (Y := (op Q, b)) (Z := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)

/-- The actual native fine open row of the same joint Model diagram. -/
def boundedFlatCoefficientFullOpenModelFunctor (_f : P ⟶ Q) : Under R ⥤ Model.{u+1} :=
  boundedFlatCoefficientSectionModelRow P

/-- Coarse-to-fine restriction uses the unchanged original joint reindexing and its literal zero. -/
def boundedFlatCoefficientOpenRestrictionModelMap (a : Under R) :
    boundedFlatCoefficientOpenModel f a ⟶ (boundedFlatCoefficientFullOpenModelFunctor f).obj a where
  functor := boundedFlatCoefficientOpenRestriction f a
  exact := boundedFlatCoefficientOpenRestriction_exact f a
  zero := boundedFlatCoefficientSectionsMap_sectionZero
    (i := (op Q, a)) (k := (op P, a)) (f.op, 𝟙 a)

/-- Coefficient change commutes literally with the actual native section restriction. -/
def boundedFlatCoefficientOpenRestrictionModelTransformation :
    boundedFlatCoefficientOpenModelFunctor f ⟶ boundedFlatCoefficientFullOpenModelFunctor f where
  app := boundedFlatCoefficientOpenRestrictionModelMap f
  naturality a b g := by
    apply Model.Hom.ext
    change underCocartesianReindex (boundedFlatCoefficientProjection R)
        (X := (op Q, a)) (Y := (op Q, b)) (𝟙 (op Q), g) ⋙
      underCocartesianReindex (boundedFlatCoefficientProjection R)
        (X := (op Q, b)) (Y := (op P, b)) (f.op, 𝟙 b) =
      underCocartesianReindex (boundedFlatCoefficientProjection R)
        (X := (op Q, a)) (Y := (op P, a)) (f.op, 𝟙 a) ⋙
      underCocartesianReindex (boundedFlatCoefficientProjection R)
        (X := (op P, a)) (Y := (op P, b)) (𝟙 (op P), g)
    rw [← underCocartesianReindex_comp, ← underCocartesianReindex_comp]
    exact congrArg (underCocartesianReindex (boundedFlatCoefficientProjection R))
      ((rowTransformation f).naturality g)

/-- The unchanged ambient fine-to-coarse Model map changes only the weak class. -/
def boundedFlatCoefficientOpenChangeWeakModelMap (a : Under R) :
    (boundedFlatCoefficientSectionModelRow Q).obj a ⟶ boundedFlatCoefficientOpenModel f a where
  functor := 𝟭 (BoundedFlatCoefficientSections (op Q, a))
  exact := Fibration.changeWeak_exact (boundedFlatCoefficientOpenNested f a)
  zero := rfl

/-- The same fine-to-coarse maps are natural in every original coefficient arrow. -/
def boundedFlatCoefficientOpenChangeWeakModelTransformation :
    boundedFlatCoefficientSectionModelRow Q ⟶ boundedFlatCoefficientOpenModelFunctor f where
  app := boundedFlatCoefficientOpenChangeWeakModelMap f
  naturality a b g := by
    apply Model.Hom.ext
    change boundedFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b))
      (𝟙 (op Q), g) ⋙ 𝟭 _ = 𝟭 _ ⋙
        boundedFlatCoefficientSectionsMap (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    simp only [Functor.comp_id, Functor.id_comp]

/-- Original iterated-S realization of the actual global coarse Models. -/
def boundedFlatCoefficientOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientOpenModelFunctor f ⋙ prespectrumFunctor

/-- Original iterated-S realization of the fine native open row. -/
def boundedFlatCoefficientFullOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientFullOpenModelFunctor f ⋙ prespectrumFunctor

/-- The actual restriction transformation on the same global coefficient prespectra. -/
def boundedFlatCoefficientOpenRestrictionPrespectrumTransformation :
    boundedFlatCoefficientOpenPrespectrumFunctor f ⟶
      boundedFlatCoefficientFullOpenPrespectrumFunctor f :=
  Functor.whiskerRight (boundedFlatCoefficientOpenRestrictionModelTransformation f)
    prespectrumFunctor

end Quillen.PerfectComplexes
