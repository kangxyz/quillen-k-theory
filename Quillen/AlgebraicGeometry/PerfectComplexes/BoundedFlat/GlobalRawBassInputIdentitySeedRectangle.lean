/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedCone
public import Quillen.Aglib.Topology.Path.MappedProjectionRectangle
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment
public import Quillen.Topology.Path.RetypedConeNullComparison

/-!
# Both complete original positive rectangles in the global seed carrier

The original 31-node surface and its full-reference unit shift retain every rectangle value.
The actual polynomial column meets its own cone sheet before evaluation. No endpoint-only
identification substitutes for either whole rectangle or either whole polynomial seam.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedRectangle
open CommonReferenceNerve BassH0Merge InputIdentitySeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The ordinary and unit-shifted original simplex maps, with both actual attachments retained. -/
def sheetMap (e : Bool) : C(StdSimplex ℝ (Fin 31), Carrier g) :=
  (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)).comp
      (if e then (mapParameter (anchorNode (commonUnit g))).comp
        (parameter (laurentRef g) (InputDescSimplex.nodes g))
      else parameter (laurentRef g) (InputDescSimplex.nodes g))

/-- Every point of either full simplex has the original native family value. -/
theorem sheetMap_native (e : Bool) (n : ℕ) (z : StdSimplex ℝ (Fin 31))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (sheetMap g e z) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      (prespectrumSimplexFamily (InputDescSimplex.simplex g) n (z, x)) := by
  cases e
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (parameter _ _ z)) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion,
      pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
    rfl
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (mapParameter (anchorNode (commonUnit g))
        (parameter _ _ z))) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion]
    change (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      (pointwisePrespectrumFamily _ n
        (mapParameter (CommonReferenceProduct.reanchor (commonUnit g)) (parameter _ _ z)) x) = _
    rw [pointwise_reanchor, pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
    rfl

/-- The original old positive binary rail on either sheet. -/
abbrev oldPositive (e : Bool) :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The original moving positive square rail on either sheet. -/
abbrev positiveMovement (e : Bool) :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The complete nonmonotone polynomial rail on either sheet. -/
abbrev polynomialMovement (e : Bool) :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The whole common Laurent square rail, preserving its original reverse/forward cuts. -/
abbrev laurentMovement (e : Bool) :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The original new positive binary rail on either sheet. -/
abbrev newPositive (e : Bool) :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map (sheetMap g e).continuous

/-- The entire original geometric rectangle retains its actual source and target words. -/
def rectangle (e : Bool) :
    ((positiveMovement g e).trans (polynomialMovement g e)).Homotopy
      ((oldPositive g e).symm.trans ((laurentMovement g e).trans (newPositive g e))) :=
  Path.Homotopy.mapProjectionRectangle (sheetMap g e)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Every original positive-pasting value is retained on both full-reference sheets. -/
theorem rectangle_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (rectangle g e (r, s)) x =
      (InputIdentityPositiveNull.positivePasting g).level n (r, (s, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (sheetMap g e (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s))) x = _
  rw [sheetMap_native, InputDescSimplex.plus_rectangle_lift]
  unfold InputIdentityPositiveNull.positivePasting
  symm
  apply Homotopy.RelHomotopy.transport_apply
  all_goals simp only [plusInputLeftTrack, plusInputRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm,
    InputIdentityPositiveNull.positiveMovement, InputIdentityPositiveNull.polynomialMovement,
    InputIdentityPositiveNull.oldPositive, InputIdentityPositiveNull.laurentMovement,
    InputIdentityPositiveNull.newPositive]

/-- Each complete polynomial rail meets the actual cone sheet at every movement time. -/
theorem polynomial_seam (e : Bool) (t : I) :
    polynomialMovement g e t = (InputIdentitySeedCone.square g e).parameter (t, 0) := by
  cases e
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter _ _ (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t)) =
        CutOpenCarrier.cylinderMinus _ _ _ _ _ (movement g t, 0)
    rw [CutOpenCarrier.cylinderMinus_zero, movement_attach]
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (anchorNode (commonUnit g))
        (parameter _ _ (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t))) =
        CutOpenCarrier.cylinderPlus _ _ _ _ _ (movement g t, 0)
    rw [CutOpenCarrier.cylinderPlus_zero, shifted_movement_attach]

/-- Original cone paths retyped only along the proved whole polynomial seam. -/
abbrev oldCone (e : Bool) := (InputIdentitySeedCone.square g e).rebaseOld
  (polynomialMovement g e) (polynomial_seam g e)
/-- The new original cone path retains its separately chosen tip. -/
abbrev newCone (e : Bool) := (InputIdentitySeedCone.square g e).rebaseNew
  (polynomialMovement g e) (polynomial_seam g e)

/-- The exact cone comparison retains all collapse and cancellation coordinates after retyping. -/
def coneComparison (e : Bool) : (oldCone g e).Homotopy
    ((polynomialMovement g e).trans (newCone g e)) :=
  ((InputIdentitySeedCone.square g e).rebaseMovement
    (polynomialMovement g e) (polynomial_seam g e)).coneBoundary

/-- Whole endpoint retyping leaves the actual cone-comparison interior unchanged. -/
theorem coneComparison_apply (e : Bool) (r s : I) :
    coneComparison g e (r, s) = InputIdentitySeedCone.boundary g e (r, s) :=
  (InputIdentitySeedCone.square g e).rebaseMovement_coneBoundary_apply
    (polynomialMovement g e) (polynomial_seam g e) r s

/-- The full typed cone comparison is the specified supported conePasting, at every native point. -/
theorem coneComparison_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (coneComparison g e (r, s)) x =
        (InputIdentityPositiveNull.conePasting g).level n (r, (s, x)) := by
  rw [coneComparison_apply]
  exact InputIdentitySeedCone.boundary_conePasting g e n r s x

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentitySeedRectangle
