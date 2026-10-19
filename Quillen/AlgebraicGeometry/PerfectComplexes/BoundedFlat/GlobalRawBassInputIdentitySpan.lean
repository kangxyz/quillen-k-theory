/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquare
public import Quillen.Topology.Prespectrum.PushoutIdentityFromUnitSquare

/-!
# The original global raw polynomial-span identity

The actual geometric unit square supplies the identity of the whole original polynomial
double cylinder. Both chart tracks retain the original split identity homotopy, and the
cylinder retains the full unit square. This does not construct the Bass comparison identity
square or a whole raw Bass step identity.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentity
variable (X : Scheme.{u})

/-- The original polynomial identity includes its actual functorial identity transport. -/
def polynomialHomotopy :
    Homotopy (boundedFlatPerfectPrespectrumMap (polynomial.map (𝟙 X)))
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X)))) :=
  (boundedFlatPerfectPrespectrumIdHomotopy (polynomial.obj X)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (polynomial.map_id X)).symm rfl

/-- The original Laurent identity retains its geometric and normalization pieces. -/
def laurentHomotopy :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurent.map (𝟙 X)))
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X)))) :=
  (boundedFlatPerfectPrespectrumIdHomotopy (laurent.obj X)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (laurent.map_id X)).symm rfl

/-- The actual polynomial square contracts through the two original geometric identity tracks. -/
def polynomialSquare :
    (polynomialSquareHomotopy (𝟙 X)).Square
      (coneSquareIdentityTrack (boundedFlatPerfectPrespectrumMap (projection.app X)))
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app X))
        (polynomialHomotopy X))
      ((boundedFlatPerfectPrespectrumIdHomotopy X).postcomp
        (boundedFlatPerfectPrespectrumMap (projection.app X))) := by
  refine (boundedFlatPerfectPrespectrumUnitSquare (projection.app X)).ofBoundaryLevels
    _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  have transport {A B : Scheme.{u}} (f : A ⟶ B) (p : A ⟶ A)
      (hp : p = 𝟙 A) (h : p ≫ f = f ≫ 𝟙 B) :
      (boundedFlatPerfectPrespectrumSquareHomotopy p f f (𝟙 B) h).level n =
        (boundedFlatPerfectPrespectrumSquareHomotopy (𝟙 A) f f (𝟙 B) (by simp)).level n := by
    subst p
    rfl
  exact transport (projection.app X) _ (polynomial.map_id X) _

/-- The entire original polynomial cylinder moves with both unchanged chart identity tracks. -/
def spanCylinderSquare :=
  HomotopyPushout.identicalLegIdentityCylinderSquare
    (boundedFlatPerfectPrespectrumMap (projection.app X))
    (polynomialSquareHomotopy (𝟙 X))
    (boundedFlatPerfectPrespectrumIdHomotopy X) (polynomialHomotopy X)
    (polynomialSquare X)

/-- Descent gives the identity of the actual raw span map, without replacing its cylinder. -/
def spanHomotopy : Homotopy (spanMap (𝟙 X)) (𝟙 (span X)) :=
  HomotopyPushout.identicalLegIdentityHomotopy
    (boundedFlatPerfectPrespectrumMap (projection.app X))
    (polynomialSquareHomotopy (𝟙 X))
    (boundedFlatPerfectPrespectrumIdHomotopy X) (polynomialHomotopy X)
    (polynomialSquare X)

/-- Every positive-chart time is exactly the original polynomial identity time. -/
theorem spanHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n) :
    (spanHomotopy X).level n
      (r, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n x) =
      (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n
          ((polynomialHomotopy X).level n (r, x)) := rfl

/-- Every inverse-chart time is the same unchanged polynomial identity time. -/
theorem spanHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n) :
    (spanHomotopy X).level n
      (r, (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n x) =
      (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X))).map n
          ((polynomialHomotopy X).level n (r, x)) := rfl

/-- The whole original overlap keeps both independent coordinates of its constructed square. -/
theorem spanHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (spanHomotopy X).level n
      (r, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (projection.app X))
        (boundedFlatPerfectPrespectrumMap (projection.app X)) n (s, x)) =
      (spanCylinderSquare X).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentity
