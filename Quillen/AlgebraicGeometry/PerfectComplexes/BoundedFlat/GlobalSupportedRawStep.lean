/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportHomotopy

/-!
# The objectwise supported raw Bass step and Laurent seed

The actual supported comparison has its mapping cone and parameter-looped first stage.
The specified source-null retains the original positive split composition followed by the
literal cone null. The original forward Laurent scalar acts on the actual supported
pullback, and its chosen-zero exact realization gives the seed by that specified null.
This constructs objectwise data only: whole three-row null comparisons and localization
naturality are additional results, not hypotheses silently supplied here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass

/-- The original parameter-looped cone of the actual supported raw comparison. -/
def step (A : Scheme.QuasiCompactOpenPairs.{u}) : LoopPrespectrum.{u+1} :=
  parameterLooping (mappingCone (comparison A))

/-- The actual positive polynomial source leg into the raw double cylinder. -/
def sourceLeg (A : Scheme.QuasiCompactOpenPairs.{u}) : rawSpectrum A.obj ⟶ span A :=
  rawMap (Geometry.projection A) ≫ HomotopyPushout.inl _ _

/-- The positive source leg recovers its actual supported geometric composite. -/
theorem sourceLeg_comparison (A : Scheme.QuasiCompactOpenPairs.{u}) :
    sourceLeg A ≫ comparison A = rawMap (Geometry.projection A) ≫ rawMap (Geometry.plus A) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The chosen source-null retains the original positive split track and literal cone null. -/
def sourceNull (A : Scheme.QuasiCompactOpenPairs.{u}) :
    Homotopy (rawMap (Geometry.laurentProjection A) ≫ mappingConeInclusion (comparison A))
      (zeroHom (rawSpectrum A.obj) (mappingCone (comparison A))) := by
  have N := Homotopy.precomp (sourceLeg A) (mappingConeHomotopy (comparison A))
  change Homotopy ((sourceLeg A ≫ comparison A) ≫ mappingConeInclusion (comparison A))
    (zeroHom _ _) at N
  exact ((plusHomotopy A).postcomp (mappingConeInclusion (comparison A))).trans
    (N.cast (congrArg (fun f => f ≫ mappingConeInclusion (comparison A))
      (sourceLeg_comparison A)) rfl)

/-- Every null time retains the original positive half-clock and the literal cone half-clock. -/
theorem sourceNull_apply (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ) (s : unitInterval)
    (x : (rawSpectrum A.obj).space n) :
    (sourceNull A).level n (s, x) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        (mappingConeInclusion (comparison A)).map n
          ((plusHomotopy A).level n
            (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else (mappingConeHomotopy (comparison A)).level n
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩, (sourceLeg A).map n x) := by
  change (ContinuousMap.HomotopyRel.trans _ _) (s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- The same original scalar automorphism acts on the actual supported geometric pullback. -/
def pullbackUnitIso {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    (r : (Γ(A.obj.right, ⊤))ˣ) :
    boundedFlatPerfectSupportedPullback p ≅ boundedFlatPerfectSupportedPullback p :=
  onFunctor (boundedFlatPerfectSupportedPullback p)
    (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r)

/-- Forgetting support keeps the whole original termwise forward scalar component. -/
theorem pullbackUnitIso_hom_original {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    (r : (Γ(A.obj.right, ⊤))ˣ) (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (boundedFlatPerfectSupported A.obj.hom).ι.map ((pullbackUnitIso p r).hom.app K) =
      (complexGlobalUnitIso A.obj.right r).hom.app
        ((boundedFlatPerfectSupportedPullback p).obj K).obj := by
  simp only [pullbackUnitIso, onFunctor_hom_app, boundedFlatPerfectSupportedGlobalUnitIso,
    CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app,
    CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.whiskerLeft_app, ObjectProperty.ι_obj]

/-- The original exact realization keeps the entire normalized supported scalar track. -/
def pullbackUnitHomotopy {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    (r : (Γ(A.obj.right, ⊤))ˣ) : Homotopy (rawMap p) (rawMap p) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectSupportedPullback_exact p)
    (boundedFlatPerfectSupportedPullback_exact p) (pullbackUnitIso p r)

/-- The forward coordinate is the existing scalar from the actual second Laurent projection. -/
def unitHomotopy (A : Scheme.QuasiCompactOpenPairs.{u}) :
    Homotopy (rawMap (Geometry.laurentProjection A)) (rawMap (Geometry.laurentProjection A)) :=
  pullbackUnitHomotopy (Geometry.laurentProjection A)
    (GlobalSchemeLaurentTrack.laurentScalar (op A.obj.obj.right))

/-- The objectwise supported raw seed, using exactly the specified positive source-null. -/
def transition (A : Scheme.QuasiCompactOpenPairs.{u}) : rawSpectrum A.obj ⟶ step A :=
  ((unitHomotopy A).postcomp (mappingConeInclusion (comparison A))).nullLoopMap (sourceNull A)

/-- Every original unit time and both null legs remain in the entire resulting loop. -/
theorem transition_apply (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
    (x : (rawSpectrum A.obj).space n) (s : unitInterval) :
    Path.toContinuousMap ((transition A).map n x) s =
      (((unitHomotopy A).postcomp (mappingConeInclusion (comparison A))).conjugateToZero
        (sourceNull A)).level n (s, x) := rfl

end Quillen.PerfectComplexes.GlobalSupportedRawBass
