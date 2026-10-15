/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassGeometricComparison
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Original polynomial source-leg movement under bounded-flat inclusion

The actual inclusion normalization track moves the original Bass source leg through the perfect
polynomial pushout. Composing with its unchanged cone nullhomotopy keeps both parameters.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The old source leg reaches the literal perfect positive polynomial endpoint. -/
theorem boundedFlatPerfectBassSourceLeg_span :
    boundedFlatBassSourceLeg R ≫ boundedFlatPerfectFlatPullbackPushoutMap
      (polynomialProjection R) (polynomialProjection R) =
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
      exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (Polynomial R)))) (boundedFlatPerfectInclusion_exact _)) ≫
      HomotopyPushout.inl (perfectFlatPrespectrumMap (polynomialProjection R))
        (perfectFlatPrespectrumMap (polynomialProjection R)) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The actual polynomial inclusion track moves the original source leg into the perfect model. -/
def boundedFlatPerfectBassSourceLegHomotopy :
    Homotopy (boundedFlatBassSourceLeg R ≫ boundedFlatPerfectFlatPullbackPushoutMap
      (polynomialProjection R) (polynomialProjection R))
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
      (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫ bassSourceLeg R) :=
  ((boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R)).postcomp
    (HomotopyPushout.inl (perfectFlatPrespectrumMap (polynomialProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R)))).cast
        (boundedFlatPerfectBassSourceLeg_span R).symm (Category.assoc _ _ _)

/-- The actual source-leg movement through the unchanged perfect cone nullhomotopy. -/
def boundedFlatPerfectBassSourceLegConeSquare :=
  Homotopy.Square.interchange (boundedFlatPerfectBassSourceLegHomotopy R)
    (mappingConeHomotopy (bassSquareComparison R))

/-- The two independent original geometric and cone parameters are retained literally. -/
theorem boundedFlatPerfectBassSourceLegConeSquare_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatPerfectBassSourceLegConeSquare R).level n (r, (s, x)) =
      (mappingConeHomotopy (bassSquareComparison R)).level n
        (s, (boundedFlatPerfectBassSourceLegHomotopy R).level n (r, x)) := rfl

/-- The actual source-leg cone square gives its genuine whole pasted boundary. -/
def boundedFlatPerfectBassSourceLegConeBoundary :=
  (boundedFlatPerfectBassSourceLegConeSquare R).toBoundary

end Quillen.PerfectComplexes
