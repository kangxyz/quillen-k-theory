/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportSections


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenConeComparison
public import Quillen.Aglib.CategoryTheory.ObjectProperty.LiftInclusion
public import Quillen.Waldhausen.SmallModel.Composition
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramZeroNull
public import Quillen.Topology.Prespectrum.ConeStableNaturality
public import Quillen.Topology.Prespectrum.ConeDescNaturality

/-!
# Original native support, ambient and coarse localization Models

Support is acyclicity on the actual native open, hence the complement of that
open on each coefficient fiber. Its original inclusion and identity change of
weakness use the same joint zero. The unique weak zero-to-inclusion transformation
gives the coefficient-natural whole null. Actual geometric fibration and exact
evaluation equivalences prove stability of this same initial cone descent.
No cofinality, completion or classical identification is assumed here.
-/
@[expose] public section

open Quillen.Waldhausen


open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.LoopPrespectrum HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- The original fine supported Model, retaining the restricted joint zero. -/
def boundedFlatCoefficientSupportedModel (a : Under R) : Model.{u+1} :=
  boundedFlatCoefficientSupportedSectionModel (schemeMap f a)

/-- The original coefficient arrow restricted to precisely the actual closed support. -/
def boundedFlatCoefficientSupportedModelMap {a b : Under R} (g : a ⟶ b) :
    boundedFlatCoefficientSupportedModel f a ⟶ boundedFlatCoefficientSupportedModel f b :=
  boundedFlatCoefficientSupportedSectionModelMap (schemeMap f a) (schemeMap f b)
    (i := (op Q, a)) (k := (op Q, b)) (𝟙 (op Q), g)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g))
    (boundedFlatCoefficientOpenSquare f g)

/-- Actual supported Models form the strict original native coefficient diagram. -/
def boundedFlatCoefficientSupportedModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatCoefficientSupportedModel f
  map := boundedFlatCoefficientSupportedModelMap f
  map_id a := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_id (schemeMap f a)
      (boundedFlatCoefficientOpenPairMap f (𝟙 a)).hom.left
      (Arrow.w (boundedFlatCoefficientOpenPairMap f (𝟙 a)).hom)
  map_comp {a b c} g h := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_comp
      (schemeMap f a) (schemeMap f b) (schemeMap f c)
      (i := (op Q, a)) (k := (op Q, b)) (t := (op Q, c))
      (𝟙 (op Q), g) (𝟙 (op Q), h)
      (boundedFlatCoefficientOpenPairMap f g).hom.left
      (boundedFlatCoefficientOpenPairMap f h).hom.left
      (boundedFlatCoefficientOpenPairMap f (g ≫ h)).hom.left
      (Arrow.w (boundedFlatCoefficientOpenPairMap f g).hom)
      (Arrow.w (boundedFlatCoefficientOpenPairMap f h).hom)
      (Arrow.w (boundedFlatCoefficientOpenPairMap f (g ≫ h)).hom)

/-- Forgetting support after evaluation keeps the original bounded-flat complex literally. -/
theorem boundedFlatCoefficientSupportedEvaluation_forget_to_boundedFlat (a : Under R) :
    boundedFlatCoefficientSupportedEvaluation (schemeMap f a) ⋙ ObjectProperty.ιOfLE
        (show boundedFlatPerfectSupported (schemeMap f a) ≤ boundedFlatPerfect (space (op Q, a))
          from fun _ h ↦ h.1) =
      (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedFlatCoefficientOriginalEvaluation (op Q, a) := by
  unfold boundedFlatCoefficientSupportedEvaluation
  exact Quillen.ObjectProperty.lift_comp_ιOfLE_comp
    (boundedFlatPerfectSupported (schemeMap f a)) (boundedFlatPerfect (space (op Q, a)))
    (fun _ h ↦ h.1) (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedFlatCoefficientOriginalEvaluation (op Q, a))
    (fun S ↦ ⟨((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj S.obj).property,
      S.property⟩)

/-- The original support inclusion is exact after its unchanged geometric evaluation. -/
theorem boundedFlatCoefficientSupportedForget_evaluation_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (boundedFlatPerfectWaldhausen (space (op Q, a))).cof
      (boundedFlatPerfectWaldhausen (space (op Q, a))).weq
      ((boundedFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedFlatCoefficientOriginalEvaluation (op Q, a)) := by
  rw [← boundedFlatCoefficientSupportedEvaluation_forget_to_boundedFlat f a]
  exact (boundedFlatCoefficientSupportedEvaluation_exact (schemeMap f a)).comp
    (subcategoryInclusion_exact _ _ (fun _ h ↦ h.1))

/-- The actual supported inclusion preserves zero, both morphism classes and pushouts. -/
theorem boundedFlatCoefficientSupportedForget_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (boundedFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι where
  zero hx := by
    let := boundedFlatCoefficientOriginalEvaluation_isEquivalence (op Q, a)
    exact IsZero.of_full_of_faithful_of_isZero
      (boundedFlatCoefficientOriginalEvaluation (op Q, a)) _
      ((boundedFlatCoefficientSupportedForget_evaluation_exact f a).zero hx)
  cofibration p hp := (boundedFlatCoefficientSupportedForget_evaluation_exact f a).cofibration p hp
  weak p hp := (boundedFlatCoefficientSupportedForget_evaluation_exact f a).weak p hp
  pushout hi hp := by
    let := boundedFlatCoefficientOriginalEvaluation_isEquivalence (op Q, a)
    apply IsPushout.of_map_of_faithful (boundedFlatCoefficientOriginalEvaluation (op Q, a))
    exact (boundedFlatCoefficientSupportedForget_evaluation_exact f a).pushout hi hp

/-- The original support inclusion is a literal joint-zero-preserving Model arrow. -/
def boundedFlatCoefficientSupportedForgetModelMap (a : Under R) :
    boundedFlatCoefficientSupportedModel f a ⟶ boundedFlatCoefficientSectionModel (op Q, a) where
  functor := (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι
  exact := boundedFlatCoefficientSupportedForget_exact f a
  zero := rfl

/-- Original support inclusion is natural under the actual coefficient reindexing. -/
def boundedFlatCoefficientSupportedForgetModelTransformation :
    boundedFlatCoefficientSupportedModelFunctor f ⟶ boundedFlatCoefficientSectionModelRow Q where
  app := boundedFlatCoefficientSupportedForgetModelMap f
  naturality a b g := by
    apply Model.Hom.ext
    exact boundedFlatCoefficientSupportedSectionsMap_forget (schemeMap f a) (schemeMap f b)
      (𝟙 (op Q), g) (boundedFlatCoefficientOpenPairMap f g).hom.left
      (Arrow.w (boundedFlatCoefficientOpenPairMap f g).hom)

/-- The actual ambient native coefficient prespectrum row. -/
def boundedFlatCoefficientAmbientPrespectrumFunctor (Q : Over (Spec R)) :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSectionModelRow Q ⋙ prespectrumFunctor

/-- Original iterated-S realization of the actual supported native Models. -/
def boundedFlatCoefficientSupportedPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatCoefficientSupportedModelFunctor f ⋙ prespectrumFunctor

/-- Realize precisely the original supported inclusion. -/
def boundedFlatCoefficientSupportedForgetPrespectrumTransformation :
    boundedFlatCoefficientSupportedPrespectrumFunctor f ⟶
      boundedFlatCoefficientAmbientPrespectrumFunctor Q :=
  Functor.whiskerRight (boundedFlatCoefficientSupportedForgetModelTransformation f)
    prespectrumFunctor

/-- Realize the unchanged ambient identity change to coarse relative-open weakness. -/
def boundedFlatCoefficientAmbientOpenPrespectrumTransformation :
    boundedFlatCoefficientAmbientPrespectrumFunctor Q ⟶
      boundedFlatCoefficientOpenPrespectrumFunctor f :=
  Functor.whiskerRight (boundedFlatCoefficientOpenChangeWeakModelTransformation f)
    prespectrumFunctor

/-- The unique original joint-zero-to-supported-inclusion transformation. -/
def boundedFlatCoefficientSupportedZeroToOpen (a : Under R) :
    (Functor.const (BoundedFlatCoefficientSupportSections f a)).obj
        (boundedFlatCoefficientSectionWaldhausen (op Q, a)).zero ⟶
      (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι where
  app S := (boundedFlatCoefficientSectionWaldhausen (op Q, a)).isZero.to_ S.obj
  naturality _ _ _ := (boundedFlatCoefficientSectionWaldhausen (op Q, a)).isZero.eq_of_src _ _

/-- Actual support makes this exact original zero-to-image transformation coarse weak. -/
theorem boundedFlatCoefficientSupportedZeroToOpen_weak (a : Under R)
    (S : BoundedFlatCoefficientSupportSections f a) :
    (boundedFlatCoefficientOpenModel f a).waldhausen.weq
      ((boundedFlatCoefficientSupportedZeroToOpen f a).app S) := by
  have hZ : IsZero ((restrict (schemeMap f a)).obj
      ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).obj
        (boundedFlatCoefficientSectionWaldhausen (op Q, a)).zero).obj) :=
    (restrict (schemeMap f a)).map_isZero ((boundedFlatPerfect (space (op Q, a))).ι.map_isZero
      ((boundedFlatCoefficientOriginalEvaluation_exact (op Q, a)).zero
        (boundedFlatCoefficientSectionWaldhausen (op Q, a)).isZero))
  change QuasiIso ((restrict (schemeMap f a)).map
    ((boundedFlatCoefficientOriginalEvaluation (op Q, a)).map
      ((boundedFlatCoefficientSupportedZeroToOpen f a).app S)).hom)
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr (S.property n)

/-- Reverse the same weak zero-to-inclusion realization, retaining all original null times. -/
def boundedFlatCoefficientSupportedOpenDiagramNull :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f)
      (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f) :=
  modelDiagramZeroNull (boundedFlatCoefficientSupportedForgetModelTransformation f)
    (boundedFlatCoefficientOpenChangeWeakModelTransformation f)
    (fun a ↦ boundedFlatCoefficientSupportedZeroToOpen f a)
    (fun a ↦ boundedFlatCoefficientSupportedZeroToOpen_weak f a)

/-- The same complete original null descends from the original supported-inclusion cone. -/
def boundedFlatCoefficientSupportedOpenConeComparison :
    mappingConeDiagram (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f) ⟶
      boundedFlatCoefficientOpenPrespectrumFunctor f :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy
    (boundedFlatCoefficientSupportedOpenDiagramNull f).naturality

/-- Original supported evaluation followed by the actual geometric acyclic conversion. -/
def boundedFlatCoefficientSupportAcyclicEvaluation (a : Under R) :
    BoundedFlatCoefficientSupportSections f a ⥤
      AcyclicCategory (boundedFlatPerfectOpenNested (schemeMap f a)) :=
  boundedFlatCoefficientSupportedEvaluation (schemeMap f a) ⋙
    boundedFlatPerfectSupportedToAcyclic (schemeMap f a)

/-- Actual support evaluation is exact into the inherited fine acyclic Model. -/
theorem boundedFlatCoefficientSupportAcyclicEvaluation_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).cof
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).weq
      (boundedFlatCoefficientSupportAcyclicEvaluation f a) :=
  (boundedFlatCoefficientSupportedEvaluation_exact (schemeMap f a)).comp
    (boundedFlatPerfectSupportedToAcyclic_exact (schemeMap f a))

/-- Evaluation preserves the actual supported inclusion before common-universe lifting. -/
theorem boundedFlatCoefficientSupportAcyclicEvaluation_inclusion (a : Under R) :
    boundedFlatCoefficientSupportAcyclicEvaluation f a ⋙
        acyclicInclusion (boundedFlatPerfectOpenNested (schemeMap f a)) =
      (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedFlatCoefficientOriginalEvaluation (op Q, a) := by
  rw [boundedFlatCoefficientSupportAcyclicEvaluation, Functor.assoc,
    boundedFlatPerfectSupportedToAcyclic_comp_inclusion,
    boundedFlatCoefficientSupportedEvaluation_forget_to_boundedFlat]

/-- The same actual supported-to-acyclic functor is the forward map of a genuine equivalence. -/
def boundedFlatCoefficientSupportAcyclicEquivalence (a : Under R) :
    BoundedFlatCoefficientSupportSections f a ≌
      AcyclicCategory (boundedFlatPerfectOpenNested (schemeMap f a)) :=
  ((boundedFlatCoefficientSupportedSectionEquivalence (schemeMap f a)).trans
    (boundedFlatPerfectAcyclicSupportedEquivalence (schemeMap f a)).symm).changeFunctor
      (eqToIso (congrArg (fun F ↦ F ⋙ boundedFlatPerfectSupportedToAcyclic (schemeMap f a))
        (boundedFlatCoefficientSupportedSectionEquivalence_functor (schemeMap f a))))

/-- Its original inverse retains the two proved exact inverse functors. -/
theorem boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).cof
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a)).weq
      (boundedFlatCoefficientSupportAcyclicEquivalence f a).inverse :=
  (boundedFlatPerfectAcyclicToSupported_exact (schemeMap f a)).comp
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))

/-- The restricted joint zero evaluates to the inherited geometric acyclic zero literally. -/
theorem boundedFlatCoefficientSupportAcyclicEvaluation_zero (a : Under R) :
    (boundedFlatCoefficientSupportAcyclicEvaluation f a).obj
        (boundedFlatCoefficientSupportedModel f a).waldhausen.zero =
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).zero := by
  apply ObjectProperty.FullSubcategory.ext
  have h := congrArg (fun F ↦ F.obj (boundedFlatCoefficientSupportedModel f a).waldhausen.zero)
    (boundedFlatCoefficientSupportAcyclicEvaluation_inclusion f a)
  exact h.trans (boundedFlatCoefficientOriginalEvaluation_sectionZero (op Q, a))

private def supportAcyclicSmallEquivalence (a : Under R) :=
  (boundedFlatCoefficientSupportAcyclicEquivalence f a).trans AsSmall.equiv

private theorem supportAcyclicSmall_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedModel f a).waldhausen.cof
      (boundedFlatCoefficientSupportedModel f a).waldhausen.weq
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel.cof
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel.weq
      (supportAcyclicSmallEquivalence f a).functor :=
  (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a).comp
    (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel_up_exact

private theorem supportAcyclicSmall_inverse_exact (a : Under R) :
    IsExact (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel.cof
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel.weq
      (boundedFlatCoefficientSupportedModel f a).waldhausen.cof
      (boundedFlatCoefficientSupportedModel f a).waldhausen.weq
      (supportAcyclicSmallEquivalence f a).inverse :=
  (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel_down_exact.comp
    (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a)

private def supportAcyclicModelMap (a : Under R) :
    boundedFlatCoefficientSupportedModel f a ⟶
      modelOf (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) where
  functor := (supportAcyclicSmallEquivalence f a).functor
  exact := supportAcyclicSmall_exact f a
  zero := congrArg AsSmall.up.obj (boundedFlatCoefficientSupportAcyclicEvaluation_zero f a)

private def ambientSmallEquivalence (a : Under R) :=
  (boundedFlatCoefficientSectionEquivalence (op Q, a)).trans AsSmall.equiv

private theorem ambientSmall_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel.cof
      (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel.weq
      (ambientSmallEquivalence (Q := Q) a).functor :=
  (boundedFlatCoefficientOriginalEvaluation_exact (op Q, a)).comp
    (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel_up_exact

private theorem ambientSmall_inverse_exact (a : Under R) :
    IsExact (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel.cof
      (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel.weq
      (boundedFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (ambientSmallEquivalence (Q := Q) a).inverse :=
  (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel_down_exact.comp
    (boundedFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))

private def ambientEvaluationModelMap (a : Under R) :
    boundedFlatCoefficientSectionModel (op Q, a) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op Q, a))) where
  functor := (ambientSmallEquivalence (Q := Q) a).functor
  exact := ambientSmall_exact a
  zero := congrArg AsSmall.up.obj (boundedFlatCoefficientOriginalEvaluation_sectionZero (op Q, a))

private theorem openSmall_exact (a : Under R) :
    IsExact (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel.cof
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel.weq
      (ambientSmallEquivalence (Q := Q) a).functor :=
  (boundedFlatCoefficientOpenEvaluation_coarse_exact f a).comp
    (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel_up_exact

private theorem openSmall_inverse_exact (a : Under R) :
    IsExact (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel.cof
      (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel.weq
      (boundedFlatCoefficientOpenWaldhausen f a).cof
      (boundedFlatCoefficientOpenWaldhausen f a).weq
      (ambientSmallEquivalence (Q := Q) a).inverse :=
  (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel_down_exact.comp
    (boundedFlatCoefficientOpenEquivalence_inverse_exact f a)

private def openEvaluationModelMap (a : Under R) :
    boundedFlatCoefficientOpenModel f a ⟶
      modelOf (boundedFlatPerfectOpenWaldhausen (schemeMap f a)) where
  functor := (ambientSmallEquivalence (Q := Q) a).functor
  exact := openSmall_exact f a
  zero := (ambientEvaluationModelMap (Q := Q) a).zero

private theorem evaluation_inclusion (a : Under R) :
    boundedFlatCoefficientSupportedForgetModelMap f a ≫ ambientEvaluationModelMap a =
      supportAcyclicModelMap f a ≫
        modelMap _ _ (acyclicInclusion_exact
          (boundedFlatPerfectOpenNested (schemeMap f a))) rfl := by
  apply Model.Hom.ext
  exact smallModelFunctor_square (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedFlatCoefficientOriginalEvaluation (op Q, a))
    (boundedFlatCoefficientSupportAcyclicEvaluation f a)
    (acyclicInclusion (boundedFlatPerfectOpenNested (schemeMap f a)))
    (boundedFlatCoefficientSupportAcyclicEvaluation_inclusion f a).symm

private theorem evaluation_changeWeak (a : Under R) :
    boundedFlatCoefficientOpenChangeWeakModelMap f a ≫ openEvaluationModelMap f a =
      ambientEvaluationModelMap a ≫ modelMap _ _
        (changeWeak_exact (boundedFlatPerfectOpenNested (schemeMap f a)))
        (boundedFlatPerfectOpenNested (schemeMap f a)).zero_eq.symm := by
  apply Model.Hom.ext
  change 𝟭 _ ⋙ (ambientSmallEquivalence (Q := Q) a).functor =
    (ambientSmallEquivalence (Q := Q) a).functor ⋙ 𝟭 _
  rw [Functor.id_comp, Functor.comp_id]

private def supportEvaluationSquare (a : Under R) :
    Arrow.mk ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a))) :=
  Arrow.homMk (prespectrumMap (supportAcyclicModelMap f a))
    (prespectrumMap (ambientEvaluationModelMap a))
    ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (evaluation_inclusion f a)).trans
        (prespectrumFunctor.map_comp _ _))).symm

private theorem null_evaluation (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    (prespectrumMap (openEvaluationModelMap f a)).map n
        (((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a))).level n
        (s, (prespectrumMap (supportAcyclicModelMap f a)).map n x) := by
  let N := boundedFlatPerfectOpenNested (schemeMap f a)
  let F := boundedFlatCoefficientSupportedForgetModelMap f a ≫
    boundedFlatCoefficientOpenChangeWeakModelMap f a
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  have hs : F ≫ openEvaluationModelMap f a = supportAcyclicModelMap f a ≫ G := by
    apply Model.Hom.ext
    apply smallModelFunctor_square F.functor (boundedFlatCoefficientOriginalEvaluation (op Q, a))
      (boundedFlatCoefficientSupportAcyclicEvaluation f a) (acyclicInclusion N)
    exact (congrArg (fun K ↦ K ⋙ boundedFlatCoefficientOriginalEvaluation (op Q, a))
      (Functor.comp_id (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι)).trans
        (boundedFlatCoefficientSupportAcyclicEvaluation_inclusion f a).symm
  let θ : (Quillen.Waldhausen.IteratedS.zeroHom
      (modelOf (acyclicStructure N)) (modelOf N.coarse)).functor ⟶ G.functor :=
    whiskerLeft AsSmall.down (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up)
  have hθ : ∀ A, (modelOf N.coarse).waldhausen.weq (θ.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak N (AsSmall.down.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G (supportAcyclicModelMap f a)
    (openEvaluationModelMap f a) hs (boundedFlatCoefficientSupportedZeroToOpen f a) θ
    (boundedFlatCoefficientSupportedZeroToOpen_weak f a) hθ n
  exact congrArg (fun H ↦ H (unitInterval.symm s, x)) h

/-- Genuine geometric fibration proves stability of the exact original native support cone. -/
theorem boundedFlatCoefficientSupportedOpenConeComparison_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedOpenConeComparison f).app a) := by
  have he : mappingConeMap (supportEvaluationSquare f a) ≫
      boundedFlatPerfectOpenConeComparison (schemeMap f a) =
    (boundedFlatCoefficientSupportedOpenConeComparison f).app a ≫
      prespectrumMap (openEvaluationModelMap f a) :=
    mappingConeDesc_naturality (supportEvaluationSquare f a)
      ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
      (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
      (prespectrumMap (openEvaluationModelMap f a))
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a)))
      ((prespectrumFunctor.map_comp _ _).symm.trans
        ((congrArg prespectrumFunctor.map (evaluation_changeWeak f a)).trans
          (prespectrumFunctor.map_comp _ _))).symm (null_evaluation f a)
  have hs := ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientSupportedModel f a)
    (W := modelOf (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))))
    (supportAcyclicSmallEquivalence f a) (supportAcyclicSmall_exact f a)
    (supportAcyclicSmall_inverse_exact f a) (supportAcyclicModelMap f a).zero
  have ha := ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientSectionModel (op Q, a))
    (W := modelOf (boundedFlatPerfectWaldhausen (space (op Q, a))))
    (ambientSmallEquivalence (Q := Q) a) (ambientSmall_exact a)
    (ambientSmall_inverse_exact a) (ambientEvaluationModelMap (Q := Q) a).zero
  have hc := (mappingConeMap_isStableEquivalence_of_excision (supportEvaluationSquare f a)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _)
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) hs ha).comp
      (boundedFlatPerfectOpenConeComparison_isStableEquivalence (schemeMap f a))
  rw [he] at hc
  have ho := ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientOpenModel f a)
    (W := modelOf (boundedFlatPerfectOpenWaldhausen (schemeMap f a)))
    (ambientSmallEquivalence (Q := Q) a) (openSmall_exact f a) (openSmall_inverse_exact f a)
    (openEvaluationModelMap f a).zero
  intro d
  let : IsIso ((stableHomotopyFunctor d).map (prespectrumMap (openEvaluationModelMap f a))) :=
    ho d
  have hd := hc d
  rw [Functor.map_comp] at hd
  exact (isIso_comp_right_iff _ _).mp hd

end Quillen.PerfectComplexes
