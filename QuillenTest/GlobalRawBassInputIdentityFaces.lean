/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierTop
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierBottom

/-! Whole original terminal, Laurent-unit, and unpaused span-unit carrier face regression. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputIdentityFaces
variable (X : Scheme.{u})

/-- The complete original projection face retains every native level and both times. -/
theorem original_projection (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
      (InputIdentityCarrierProjection.face X)
        n ((s, t), x) =
      (coneSquareIdentityTrack (comparison X)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x)) :=
  InputIdentityCarrierProjection.face_native X n s t x

/-- The complete original bottom face retains every native level and both times. -/
theorem original_bottom (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.face X)
        n ((r, t), x) =
      (Homotopy.precomp (comparison X) (InputIdentity.laurentHomotopy X)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x)) :=
  InputIdentityCarrierBottom.face_native X n r t x

/-- The complete original top face retains every native level and both times. -/
theorem original_top (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.face X)
        n ((r, t), x) =
      ((InputIdentity.spanHomotopy X).postcomp (comparison X)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x)) :=
  InputIdentityCarrierTop.face_native X n r t x

/-- Both terminal chart joins are actual carrier equalities before any evaluation. -/
theorem terminal_chart_joins (s : unitInterval) :
    InputIdentityCarrierProjection.face X (s, 0) =
      InputIdentityCarrierCharts.chartFace X plus plus_projection (1, s) ∧
    InputIdentityCarrierProjection.face X (s, 1) =
      InputIdentityCarrierCharts.chartFace X minus minus_projection (1, s) :=
  ⟨DFunLike.congr_fun (InputIdentityCarrierProjection.plus_seam X) s,
    DFunLike.congr_fun (InputIdentityCarrierProjection.minus_seam X) s⟩

/-- The unpaused span-unit carrier keeps the structure time independent of both face coordinates. -/
theorem top_independent_structure (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.face X) (n + 1)
        ((r, t), (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
          (InputIdentityCarrierTop.face X) n ((r, t), x)) z :=
  CommonReferenceNerve.compactPrespectrumFamily_structure (InputIdentityNodes.source X)
    (InputIdentityCarrierTop.face X) n (r, t) x z

end QuillenTest.GlobalRawBassInputIdentityFaces
