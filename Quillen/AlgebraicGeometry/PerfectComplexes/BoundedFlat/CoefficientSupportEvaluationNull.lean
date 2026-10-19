/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportLocalizationModels

/-!
# Original coefficient evaluation preserves the entire support null

The three evaluation arrows use the original functors followed by the genuine small-model
inclusion. They retain the literal selected zeros, both original localization arrows, and every
point of the chosen null. No normalized rebase arrow replaces these raw evaluation maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- The actual supported evaluation into the original fine acyclic Model. -/
def supportAcyclicEvaluationModelMap (a : Under R) :
    boundedFlatCoefficientSupportedModel f a ⟶
      modelOf (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) where
  functor := boundedFlatCoefficientSupportAcyclicEvaluation f a ⋙ AsSmall.up
  exact := (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a).comp
    (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))).smallModel_up_exact
  zero := congrArg AsSmall.up.obj (boundedFlatCoefficientSupportAcyclicEvaluation_zero f a)

/-- Original ambient evaluation with its literal chosen zero and common-universe inclusion. -/
def ambientOriginalEvaluationModelMap (a : Under R) :
    boundedFlatCoefficientSectionModel (op Q, a) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op Q, a))) where
  functor := boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙ AsSmall.up
  exact := (boundedFlatCoefficientOriginalEvaluation_exact (op Q, a)).comp
    (boundedFlatPerfectWaldhausen (space (op Q, a))).smallModel_up_exact
  zero := congrArg AsSmall.up.obj (boundedFlatCoefficientOriginalEvaluation_sectionZero (op Q, a))

/-- The same original evaluation, carrying the actual coarser weak equivalences. -/
def coarseOriginalEvaluationModelMap (a : Under R) :
    boundedFlatCoefficientOpenModel f a ⟶
      modelOf (boundedFlatPerfectOpenWaldhausen (schemeMap f a)) where
  functor := boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙ AsSmall.up
  exact := (boundedFlatCoefficientOpenEvaluation_coarse_exact f a).comp
    (boundedFlatPerfectOpenWaldhausen (schemeMap f a)).smallModel_up_exact
  zero := (ambientOriginalEvaluationModelMap (Q := Q) a).zero

/-- The actual supported inclusion square before applying the prespectrum functor. -/
theorem supportAcyclicEvaluationModelMap_inclusion (a : Under R) :
    boundedFlatCoefficientSupportedForgetModelMap f a ≫ ambientOriginalEvaluationModelMap a =
      supportAcyclicEvaluationModelMap f a ≫
        modelMap _ _ (acyclicInclusion_exact
          (boundedFlatPerfectOpenNested (schemeMap f a))) rfl := by
  apply Model.Hom.ext
  exact smallModelFunctor_square (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedFlatCoefficientOriginalEvaluation (op Q, a))
    (boundedFlatCoefficientSupportAcyclicEvaluation f a)
    (acyclicInclusion (boundedFlatPerfectOpenNested (schemeMap f a)))
    (boundedFlatCoefficientSupportAcyclicEvaluation_inclusion f a).symm

/-- Original evaluation commutes with the identity change of weak equivalences. -/
theorem coarseOriginalEvaluationModelMap_changeWeak (a : Under R) :
    boundedFlatCoefficientOpenChangeWeakModelMap f a ≫ coarseOriginalEvaluationModelMap f a =
      ambientOriginalEvaluationModelMap a ≫ modelMap _ _
        (changeWeak_exact (boundedFlatPerfectOpenNested (schemeMap f a)))
        (boundedFlatPerfectOpenNested (schemeMap f a)).zero_eq.symm := by
  apply Model.Hom.ext
  change 𝟭 _ ⋙ (boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙ AsSmall.up) =
    (boundedFlatCoefficientOriginalEvaluation (op Q, a) ⋙ AsSmall.up) ⋙ 𝟭 _
  rw [Functor.id_comp, Functor.comp_id]

/-- The original inclusion square at the actual prespectrum level. -/
def supportOriginalEvaluationSquare (a : Under R) :
    Arrow.mk ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a))) :=
  Arrow.homMk (prespectrumMap (supportAcyclicEvaluationModelMap f a))
    (prespectrumMap (ambientOriginalEvaluationModelMap a))
    ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (supportAcyclicEvaluationModelMap_inclusion f a)).trans
        (prespectrumFunctor.map_comp _ _))).symm

/-- Every original null time evaluates to the unchanged geometric acyclic null. -/
theorem supportOriginalEvaluationNull (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    (prespectrumMap (coarseOriginalEvaluationModelMap f a)).map n
        (((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a))).level n
        (s, (prespectrumMap (supportAcyclicEvaluationModelMap f a)).map n x) := by
  let N := boundedFlatPerfectOpenNested (schemeMap f a)
  let F := boundedFlatCoefficientSupportedForgetModelMap f a ≫
    boundedFlatCoefficientOpenChangeWeakModelMap f a
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  have hs : F ≫ coarseOriginalEvaluationModelMap f a =
      supportAcyclicEvaluationModelMap f a ≫ G := by
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
  have h := prespectrumZeroTransformationHomotopy_naturality F G
    (supportAcyclicEvaluationModelMap f a) (coarseOriginalEvaluationModelMap f a) hs
    (boundedFlatCoefficientSupportedZeroToOpen f a) θ
    (boundedFlatCoefficientSupportedZeroToOpen_weak f a) hθ n
  exact congrArg (fun H ↦ H (unitInterval.symm s, x)) h

end Quillen.PerfectComplexes
