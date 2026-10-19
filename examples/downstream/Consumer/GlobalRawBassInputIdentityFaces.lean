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

/-! Whole original terminal, Laurent-unit, and unpaused span-unit carrier face consumption. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalRawBassInputIdentityFaces
variable (X : Scheme.{u})

/-- The whole actual bottom face is consumed independently of the regression module. -/
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

/-- The whole actual top face is consumed independently of the regression module. -/
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

end Consumer.GlobalRawBassInputIdentityFaces
