/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedRawPullbackTrack
public import Quillen.Topology.Prespectrum.PushoutHomotopy

/-!
# The actual supported raw Bass square

The actual quasi-compact polynomial and Laurent open pairs carry the original supported
pullback spectra. The overlap retains the original split composition tracks, with their
positive and inverse-chart clocks. Their complete normalized Model triangles have explicit
relative comparisons with these tracks. The resulting span is the actual reduced double
cylinder, not a strict diagram surrogate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass
open SupportedTensorEvaluation
attribute [local irreducible] compositionTriangle

/-- Realize a normalized geometric triangle with its literal composite endpoint. -/
def chartHomotopy {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C)
    (i : boundedFlatPerfectSupportedPullback r ≅
      boundedFlatPerfectSupportedPullback q ⋙ boundedFlatPerfectSupportedPullback p) :
    Homotopy (rawMap r) (rawMap q ≫ rawMap p) :=
  (prespectrumTransformationHomotopy
    (F := evaluationRawMap r) (G := evaluationRawMap q ≫ evaluationRawMap p)
    (chartNormalizationIso p q r i).hom
    (fun _ ↦ (rawModel A).waldhausen.weq_iso _ inferInstance)).cast rfl
      (prespectrumFunctor.map_comp (evaluationRawMap q) (evaluationRawMap p))

/-- Equality transport in a geometric triangle retains the original complete normalized track. -/
theorem chartHomotopy_transport_level {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (h : p ≫ q = r) (n : ℕ) :
    (chartHomotopy p q r
      (eqToIso (congrArg boundedFlatPerfectSupportedPullback h).symm ≪≫
        boundedFlatPerfectSupportedPullbackCompIso p q)).level n =
      (normalizedCompositionHomotopy p q).level n := by
  subst r
  simp only [eqToIso_refl, Iso.refl_trans]
  rfl

/-- The positive chart keeps the original two-stage composition and equality transport. -/
def plusHomotopy (A : Scheme.QuasiCompactOpenPairs.{u}) :
    Homotopy (rawMap (Geometry.laurentProjection A))
      (rawMap (Geometry.projection A) ≫ rawMap (Geometry.plus A)) :=
  (compositionHomotopy (Geometry.plus A) (Geometry.projection A)).cast
    (congrArg rawMap (Geometry.plus_projection A)) rfl

/-- The inverse-coordinate chart keeps its independent original split track. -/
def minusHomotopy (A : Scheme.QuasiCompactOpenPairs.{u}) :
    Homotopy (rawMap (Geometry.laurentProjection A))
      (rawMap (Geometry.projection A) ≫ rawMap (Geometry.minus A)) :=
  (compositionHomotopy (Geometry.minus A) (Geometry.projection A)).cast
    (congrArg rawMap (Geometry.minus_projection A)) rfl

/-- Realize the exact positive Model triangle from the sealed chart interface. -/
def plusNormalizedHomotopy (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  chartHomotopy (Geometry.plus A) (Geometry.projection A) (Geometry.laurentProjection A)
    (plusPullbackIso A)

/-- Realize the exact inverse-chart Model triangle from the sealed chart interface. -/
def minusNormalizedHomotopy (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  chartHomotopy (Geometry.minus A) (Geometry.projection A) (Geometry.laurentProjection A)
    (minusPullbackIso A)

/-- The whole normalized chart is the original total track with only endpoint transport. -/
theorem chartHomotopy_eq_cast {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (h : p ≫ q = r) :
    chartHomotopy p q r
        (eqToIso (congrArg boundedFlatPerfectSupportedPullback h).symm ≪≫
          boundedFlatPerfectSupportedPullbackCompIso p q) =
      (normalizedCompositionHomotopy p q).cast (congrArg rawMap h) rfl := by
  subst r
  simp only [eqToIso_refl, Iso.refl_trans]
  rfl

/-- Recover a transported chart from its actual original split composition triangle. -/
def chartComparison {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (h : p ≫ q = r) :
    (chartHomotopy p q r
      (eqToIso (congrArg boundedFlatPerfectSupportedPullback h).symm ≪≫
        boundedFlatPerfectSupportedPullbackCompIso p q)).RelHomotopy
      ((compositionHomotopy p q).cast (congrArg rawMap h) rfl) :=
  originalPastingTransport (chartHomotopy_eq_cast p q r h).symm
    ((compositionComparison p q).cast (congrArg rawMap h) rfl)

/-- The whole original chart transport is named before projecting its dependent level. -/
theorem chartComparison_eq_original {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (h : p ≫ q = r) :
    chartComparison p q r h =
      originalPastingTransport (chartHomotopy_eq_cast p q r h).symm
        ((compositionComparison p q).cast (congrArg rawMap h) rfl) := rfl

/-- Chart equality transport retains the entire original two-time composition triangle. -/
theorem chartComparison_whole_level {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (h : p ≫ q = r) (n : ℕ) :
    ((chartComparison p q r h).level n).toContinuousMap =
      ((compositionTriangle p q).level n).toContinuousMap := by
  rw [chartComparison_eq_original, originalPastingTransport_level]
  exact (Homotopy.RelHomotopy.cast_whole_level (compositionComparison p q)
    (congrArg rawMap h) rfl n).trans (compositionComparison_whole_level p q n)

/-- The original positive split track is recovered by the actual relative composition triangle. -/
def plusComparison (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (plusNormalizedHomotopy A).RelHomotopy (plusHomotopy A) :=
  chartComparison _ _ _ (Geometry.plus_projection A)

/-- The inverse chart has its own complete relative split-track recovery. -/
def minusComparison (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (minusNormalizedHomotopy A).RelHomotopy (minusHomotopy A) :=
  chartComparison _ _ _ (Geometry.minus_projection A)

/-- The actual overlap, with the positive track reversed and the inverse track forward. -/
def squareHomotopy (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  (plusHomotopy A).symm.trans (minusHomotopy A)

/-- The supported raw span is the original reduced double cylinder. -/
def span (A : Scheme.QuasiCompactOpenPairs.{u}) : LoopPrespectrum.{u+1} :=
  HomotopyPushout.prespectrum (rawMap (Geometry.projection A)) (rawMap (Geometry.projection A))

/-- Descend the whole original supported overlap to the Laurent comparison. -/
def comparison (A : Scheme.QuasiCompactOpenPairs.{u}) : span A ⟶ rawSpectrum (Geometry.laurent A) :=
  HomotopyPushout.desc (rawMap (Geometry.projection A)) (rawMap (Geometry.projection A))
    (rawMap (Geometry.plus A)) (rawMap (Geometry.minus A)) (squareHomotopy A)

/-- Every height of the raw double cylinder is the specified original overlap track. -/
theorem comparison_cylinder (A : Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ) (s : unitInterval)
    (x : (rawSpectrum A.obj).space n) :
    (comparison A).map n
      (HomotopyPushout.cylinder (rawMap (Geometry.projection A))
        (rawMap (Geometry.projection A)) n (s, x)) =
      (squareHomotopy A).level n (s, x) := rfl

end Quillen.PerfectComplexes.GlobalSupportedRawBass
