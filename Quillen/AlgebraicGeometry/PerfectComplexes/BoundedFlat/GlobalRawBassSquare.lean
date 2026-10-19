/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack
public import Quillen.Topology.Prespectrum.PushoutHomotopy
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# The raw polynomial and Laurent Bass square on an arbitrary scheme

All four spectra and maps are the original bounded-flat geometric construction on the
actual integer-base products. The two chart paths retain the original split geometric
composition homotopies. The products are `X ×_{Spec ℤ} Spec ℤ[t]` and
`X ×_{Spec ℤ} Spec ℤ[t,t⁻¹]`, with the universe lift used by `GlobalIndex`. This is an
objectwise raw square, without a strict functoriality claim. No identification with the
separately implemented coefficient raw square is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass

/-- The original projection from the actual Laurent product. -/
def laurentProjection : laurent.{u} ⟶ 𝟭 Scheme.{u} :=
  baseProductProjection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
    (.of (ULift.{u} ℤ)))

/-- The positive chart has its original common Laurent projection. -/
theorem plus_projection (X : Scheme.{u}) :
    plus.app X ≫ projection.app X = laurentProjection.app X :=
  baseProductTransformation_projection _ _ _ _ X

/-- The inverse-coordinate chart has the same original Laurent projection. -/
theorem minus_projection (X : Scheme.{u}) :
    minus.app X ≫ projection.app X = laurentProjection.app X :=
  baseProductTransformation_projection _ _ _ _ X

/-- The original split geometric composition track of the positive chart. -/
def plusHomotopy (X : Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection.app X))
      (boundedFlatPerfectPrespectrumMap (projection.app X) ≫
        boundedFlatPerfectPrespectrumMap (plus.app X)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (plus.app X) (projection.app X)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (plus_projection X)) rfl

/-- The independent inverse-coordinate chart retains its original split track. -/
def minusHomotopy (X : Scheme.{u}) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection.app X))
      (boundedFlatPerfectPrespectrumMap (projection.app X) ≫
        boundedFlatPerfectPrespectrumMap (minus.app X)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (minus.app X) (projection.app X)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (minus_projection X)) rfl

/-- The actual raw two-chart overlap with its original signs and concatenation timing. -/
def squareHomotopy (X : Scheme.{u}) :=
  (plusHomotopy X).symm.trans (minusHomotopy X)

/-- The actual raw polynomial span is its original reduced double cylinder. -/
def span (X : Scheme.{u}) : LoopPrespectrum.{u+1} :=
  HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (projection.app X))
    (boundedFlatPerfectPrespectrumMap (projection.app X))

/-- The original two-chart track descends to the raw Laurent comparison. -/
def comparison (X : Scheme.{u}) :
    span X ⟶ originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X)) :=
  HomotopyPushout.desc (boundedFlatPerfectPrespectrumMap (projection.app X))
    (boundedFlatPerfectPrespectrumMap (projection.app X))
    (boundedFlatPerfectPrespectrumMap (plus.app X))
    (boundedFlatPerfectPrespectrumMap (minus.app X)) (squareHomotopy X)

/-- Every height of the original overlap is retained by the raw comparison. -/
theorem comparison_cylinder (X : Scheme.{u}) (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (comparison X).map n
      (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X)) n (s, x)) =
      (squareHomotopy X).level n (s, x) := rfl

end Quillen.PerfectComplexes.GlobalRawBass
