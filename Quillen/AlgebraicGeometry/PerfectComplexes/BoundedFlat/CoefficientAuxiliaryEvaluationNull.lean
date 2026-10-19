/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberLocalizationModels

/-!
# The original auxiliary-support null in its native acyclic Model

The actual intersection-support category maps to the acyclic category of the
original native auxiliary-supported nested structure. Together with the actual
small-model inclusions on ambient and coarse sections, this preserves both
localization arrows and every original null time. Independent geometric chosen
zeros are not identified; geometric K-boundary comparisons use ordinary exact
evaluation after this native same-null square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

private theorem acyclic_lift_exact {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) {W : Structure D} (N : NestedWeakEquivalences W)
    (F : C ⥤ AcyclicCategory N)
    (h : IsExact V.cof V.weq W.cof W.weq (F ⋙ acyclicInclusion N)) :
    IsExact V.cof V.weq (acyclicStructure N).cof (acyclicStructure N).weq F where
  zero hZ := IsZero.of_full_of_faithful_of_isZero (acyclicObjects N).ι _ (h.zero hZ)
  cofibration p hp := h.cofibration p hp
  weak p hp := h.weak p hp
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects N).ι (h.pushout hi hp)

/-- The original support-forget exactness lifts through the actual acyclic inclusion. -/
theorem boundedFlatCoefficientSupportedFiberToAcyclic_exact (a : Under R) :
    IsExact (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.cof
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.weq
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedFlatCoefficientSupportedFiberToAcyclic f T a) :=
  acyclic_lift_exact (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen
    (boundedFlatCoefficientSupportedOpenNested f T a)
    (boundedFlatCoefficientSupportedFiberToAcyclic f T a)
    ((boundedFlatCoefficientSupportedFiberToAcyclic_inclusion f T a).symm ▸
      boundedFlatCoefficientSupportedFiberForget_exact f T a)

/-- Actual native acyclic conversion followed by its literal common-universe inclusion. -/
def auxiliaryNativeFiberAcyclicModelMap (a : Under R) :
    boundedFlatCoefficientSupportedFiberModel f T a ⟶
      modelOf (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)) where
  functor := boundedFlatCoefficientSupportedFiberToAcyclic f T a ⋙ AsSmall.up
  exact := (boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a).comp
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).smallModel_up_exact
  zero := rfl

/-- The ambient native supported Model retains its own selected zero. -/
def auxiliaryNativeAmbientModelMap (a : Under R) :
    boundedFlatCoefficientSupportedAmbientModel T a ⟶
      modelOf (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen where
  functor := AsSmall.up
  exact := (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.smallModel_up_exact
  zero := rfl

/-- The actual coarser native Model uses the same literal small-model inclusion. -/
def auxiliaryNativeCoarseModelMap (a : Under R) :
    boundedFlatCoefficientSupportedOpenModel f T a ⟶
      modelOf (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen where
  functor := AsSmall.up
  exact := (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.smallModel_up_exact
  zero := rfl

/-- Native acyclic conversion preserves the original support-enlargement arrow. -/
theorem auxiliaryNativeFiberAcyclicModelMap_inclusion (a : Under R) :
    boundedFlatCoefficientSupportedFiberForgetModelMap f T a ≫
        auxiliaryNativeAmbientModelMap T a =
      auxiliaryNativeFiberAcyclicModelMap f T a ≫ modelMap _ _
        (acyclicInclusion_exact (boundedFlatCoefficientSupportedOpenNested f T a)) rfl := by
  apply Model.Hom.ext
  rfl

omit [IsOpenImmersion f.left] in
/-- Native small-model inclusion preserves the original change of weak equivalences. -/
theorem auxiliaryNativeCoarseModelMap_changeWeak (a : Under R) :
    boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a ≫
        auxiliaryNativeCoarseModelMap f T a =
      auxiliaryNativeAmbientModelMap T a ≫ modelMap _ _
        (changeWeak_exact (boundedFlatCoefficientSupportedOpenNested f T a))
        (boundedFlatCoefficientSupportedOpenNested f T a).zero_eq.symm := by
  apply Model.Hom.ext
  rfl

/-- The actual prespectrum square retains the original native acyclic inclusion. -/
def auxiliaryNativeFiberEvaluationSquare (a : Under R) :
    Arrow.mk ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap
        (boundedFlatCoefficientSupportedOpenNested f T a)) :=
  Arrow.homMk (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a))
    (prespectrumMap (auxiliaryNativeAmbientModelMap T a))
    ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (auxiliaryNativeFiberAcyclicModelMap_inclusion f T a)).trans
        (prespectrumFunctor.map_comp _ _))).symm

private theorem nativeAcyclicNull_square {C : Type u} [Category.{u} C]
    {V : Structure C} (N : NestedWeakEquivalences V) {W : Model.{u}}
    (F : W ⟶ (⟨Cat.of C, N.coarse⟩ : Model.{u}))
    (a : W ⟶ modelOf (acyclicStructure N))
    (c : (⟨Cat.of C, N.coarse⟩ : Model.{u}) ⟶ modelOf N.coarse)
    (hs : F ≫ c = a ≫ modelMap (acyclicStructure N) N.coarse
      (acyclicInclusion_coarse_exact N)
      (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm))
    (η : (Quillen.Waldhausen.IteratedS.zeroHom W
      (⟨Cat.of C, N.coarse⟩ : Model.{u})).functor ⟶ F.functor)
    (hη : ∀ X, N.coarse.weq (η.app X))
    (n : ℕ) (s : unitInterval) (x : (prespectrum W).space n) :
    (prespectrumMap c).map n
      ((prespectrumTransformationHomotopy η hη).level n (unitInterval.symm s, x)) =
      (acyclicPrespectrumNullhomotopy N).level n
        (s, (prespectrumMap a).map n x) := by
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  let θ : (Quillen.Waldhausen.IteratedS.zeroHom
      (modelOf (acyclicStructure N)) (modelOf N.coarse)).functor ⟶ G.functor :=
    whiskerLeft AsSmall.down.{u, u, 0}
      (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up.{u, u, 0})
  have hθ : ∀ A, (modelOf N.coarse).waldhausen.weq (θ.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak N (AsSmall.down.{u, u, 0}.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G a c hs η θ hη hθ n
  exact congrArg (fun H ↦ H (unitInterval.symm s, x)) h

/-- Every original null time maps to the original native acyclic null at the same time. -/
theorem auxiliaryNativeFiberEvaluationNull (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    (prespectrumMap (auxiliaryNativeCoarseModelMap f T a)).map n
        (((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatCoefficientSupportedOpenNested f T a)).level n
        (s, (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a)).map n x) := by
  let N := boundedFlatCoefficientSupportedOpenNested f T a
  let F := boundedFlatCoefficientSupportedFiberForgetModelMap f T a ≫
    boundedFlatCoefficientSupportedOpenChangeWeakModelMap f T a
  let G := modelMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  have hs : F ≫ auxiliaryNativeCoarseModelMap f T a =
      auxiliaryNativeFiberAcyclicModelMap f T a ≫ G := by
    apply Model.Hom.ext
    rfl
  exact nativeAcyclicNull_square N F (auxiliaryNativeFiberAcyclicModelMap f T a)
    (auxiliaryNativeCoarseModelMap f T a) hs
    (boundedFlatCoefficientSupportedFiberZeroToOpen f T a)
    (boundedFlatCoefficientSupportedFiberZeroToOpen_weak f T a) n s x

end Quillen.PerfectComplexes
