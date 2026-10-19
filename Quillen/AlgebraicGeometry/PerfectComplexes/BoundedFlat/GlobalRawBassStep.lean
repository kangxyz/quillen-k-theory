/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnit

/-!
# The integer-base raw Bass step and Laurent seed on every scheme

The target is the actual parameter-looped cone of the raw geometric comparison. Its forward
Laurent unit is conjugated by the specified positive-chart cone nullhomotopy. No strict diagram
or all-stage raw tower is identified with this objectwise construction. Its source-null uses
the original split positive-chart composition followed by the literal cone null. Comparison
with the existing coefficient raw first stage is a separate, unproved interface.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass

/-- The actual parameter-looped cone of the original raw Bass comparison. -/
def step (X : Scheme.{u}) : LoopPrespectrum.{u+1} :=
  parameterLooping (mappingCone (comparison X))

/-- The actual positive polynomial leg into the original raw double cylinder. -/
def sourceLeg (X : Scheme.{u}) :
    originalPrespectrum (boundedFlatPerfectWaldhausen X) ⟶ span X :=
  boundedFlatPerfectPrespectrumMap (projection.app X) ≫ HomotopyPushout.inl _ _

/-- The positive source leg retains the actual positive geometric composite. -/
theorem sourceLeg_comparison (X : Scheme.{u}) :
    sourceLeg X ≫ comparison X = boundedFlatPerfectPrespectrumMap (projection.app X) ≫
      boundedFlatPerfectPrespectrumMap (plus.app X) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The specified raw source-null is the original positive chart followed by the cone null. -/
def sourceNull (X : Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection.app X) ≫
      mappingConeInclusion (comparison X))
      (zeroHom (originalPrespectrum (boundedFlatPerfectWaldhausen X))
        (mappingCone (comparison X))) := by
  have N := Homotopy.precomp (sourceLeg X) (mappingConeHomotopy (comparison X))
  change Homotopy ((sourceLeg X ≫ comparison X) ≫ mappingConeInclusion (comparison X))
    (zeroHom _ _) at N
  rw [sourceLeg_comparison] at N
  exact ((plusHomotopy X).postcomp (mappingConeInclusion (comparison X))).trans N

/-- The original forward coordinate acts along the actual Laurent projection. -/
def unitHomotopy (X : Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection.app X))
      (boundedFlatPerfectPrespectrumMap (laurentProjection.app X)) :=
  boundedFlatPerfectUnitHomotopy (laurentProjection.app X)
    (GlobalSchemeLaurentTrack.laurentScalar (op X))

/-- The original raw forward Laurent seed, using precisely the specified source-null. -/
def transition (X : Scheme.{u}) :
    originalPrespectrum (boundedFlatPerfectWaldhausen X) ⟶ step X :=
  ((unitHomotopy X).postcomp (mappingConeInclusion (comparison X))).nullLoopMap (sourceNull X)

/-- Every loop time keeps the whole original unit track and both original null legs. -/
theorem transition_apply (X : Scheme.{u}) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) (s : unitInterval) :
    Path.toContinuousMap ((transition X).map n x) s =
      (((unitHomotopy X).postcomp (mappingConeInclusion (comparison X))).conjugateToZero
        (sourceNull X)).level n (s, x) := rfl

end Quillen.PerfectComplexes.GlobalRawBass
