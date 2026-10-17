/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0RectangleRails
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0RectangleNative
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitPastingLift
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTransitionNaturality

/-!
# The original direct-Laurent unit-pasting surface in the actual two-tip carrier

All ten full references, the five-piece intertwining and its internal rotation remain unchanged.
Four whole boundaries are retained. This is the actual unit constituent, not a whole J0 filler.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0UnitPasting
open CommonReferenceNerve BassH0Merge CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0RectangleRails
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The old original unit rail crosses from its ordinary to its shifted full reference. -/
abbrev oldUnit := CoefficientLaurentUnitTenNodes.V.map (unitMap P p q).continuous
/-- The new original unit rail crosses from its ordinary to its shifted full reference. -/
abbrev newUnit := CoefficientLaurentUnitTenNodes.W.map (unitMap P p q).continuous
/-- The entire ordinary Laurent movement word in the original direct-l reference. -/
abbrev lower :=
  (CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0).map
    (unitMap P p q).continuous
/-- The entire unit-shifted Laurent movement word in that same direct-l reference. -/
abbrev upper :=
  (CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1).map
    (unitMap P p q).continuous

/-- Map the literal original five-piece intertwining, without selecting another comparison. -/
def unitComparison : ((oldUnit P p q).trans (upper P p q)).Homotopy
    ((lower P p q).trans (newUnit P p q)) :=
  (CoefficientLaurentUnitPastingLift.parameter.map (unitMap P p q)).cast
    (by simp only [Path.map_trans]) (by simp only [Path.map_trans])

/-- Every interior coordinate is the unchanged original scalar unit-pasting parameter. -/
theorem unitComparison_apply (r s : I) :
    unitComparison P p q (r, s) =
      unitMap P p q (CoefficientLaurentUnitPastingLift.parameter (r, s)) := rfl

/-- Whole source boundary, retaining the shifted outer word and its original half cut. -/
theorem source (s : I) :
    unitComparison P p q (0, s) = ((oldUnit P p q).trans (upper P p q)) s :=
  (unitComparison P p q).map_zero_left s

/-- Whole target boundary, retaining the lower outer word followed by the original new unit. -/
theorem target (s : I) :
    unitComparison P p q (1, s) = ((lower P p q).trans (newUnit P p q)) s :=
  (unitComparison P p q).map_one_left s

/-- The entire left side remains the actual ordinary old terminal full node. -/
theorem left (r : I) :
    unitComparison P p q (r, 0) = unitMap P p q (StdSimplex.single 2) := by
  rw [unitComparison_apply, Path.Homotopy.source]

/-- The entire right side remains the distinct unit-shifted new terminal full node. -/
theorem right (r : I) :
    unitComparison P p q (r, 1) = unitMap P p q (StdSimplex.single 9) := by
  rw [unitComparison_apply, Path.Homotopy.target]

/-- The complete lower boundary rail agrees with the actual ordinary positive rectangle rail. -/
theorem lower_rail (s : I) : lower P p q s = laurentMovementMinus P p q s :=
  (outerMinus P p q s).symm

/-- The complete upper boundary rail agrees with the actual shifted positive rectangle rail. -/
theorem upper_rail (s : I) : upper P p q s = laurentMovementPlus P p q s :=
  (outerPlus P p q s).symm

/-- Every native value is the original cone-postcomposed unit intertwining, including n=0. -/
theorem original_value (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (unitComparison P p q (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n
      ((boundedFlatCoefficientLaurentUnitPasting P (p ≫ q)).level n
        (r, (s, x))) := by
  rw [unitComparison_apply]
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n
      (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
        (ordinary P p q) (shifted P p q) (mapParameter _ (parameter _ _ _))) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion, mapParameter_parameter,
    pointwisePrespectrumFamily_parameter]
  change (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n
    (prespectrumFamily (laurentRef P p q)
      (ModelSimplex.reanchorNodes
        (eqToIso (BassH0Merge.reference_eq P p q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q))) n
      (CoefficientLaurentUnitPastingLift.parameter (r, s), x)) = _
  rw [prespectrumFamily_reanchor, prespectrumFamily_eq]
  exact congrArg
    ((LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n)
    (CoefficientLaurentUnitPastingLift.original_lift P (p ≫ q)
      n r s x)

/-- The original unitPasting boundary transport preserves the whole carrier native surface. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (unitComparison P p q (r, s)) x =
    (CoefficientBassPositiveTransitionTrack.unitPasting P
      (p ≫ q)).level n (r, (s, x)) := by
  rw [original_value]
  unfold CoefficientBassPositiveTransitionTrack.unitPasting
  symm
  apply LoopPrespectrum.Homotopy.RelHomotopy.transport_apply
  all_goals simp only [LoopPrespectrum.Homotopy.postcomp_trans,
    CoefficientBassPositiveTransitionTrack.oldUnit, CoefficientBassPositiveTransitionTrack.newUnit,
    CoefficientBassPositiveNullTrack.laurentMovement]

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0UnitPasting
