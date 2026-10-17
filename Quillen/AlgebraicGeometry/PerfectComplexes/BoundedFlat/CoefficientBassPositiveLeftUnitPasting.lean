/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftRectangles
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftMidpointUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitPastingLift
public import Quillen.Aglib.Topology.Path.RetypedUnitComparison
/-!
# Original first and middle unit pastings in the common carrier

Both original ten-node families retain their actual firstIso or middleIso transport.
Five complete ordinary nodes and five complete shifted nodes identify each whole Laurent
movement rail. The original scalar unit comparison is then retyped along these whole rails,
without changing its five stages, internal rotation, unit coordinate, or comparison time.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitPasting
open BassH0Merge CommonReferenceNerve LaurentUnitReferenceSpecialization
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierSeed
open CoefficientBassPositiveLeftCellParameters CoefficientBassPositiveLeftRectangles
open CoefficientBassPositiveLeftMidpointUnit
open CoefficientBassPositiveJ0OuterBridge CoefficientBassPositiveJ0ShiftedBridge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- All five ordinary first references agree before taking the characteristic map. -/
theorem first_lower_nodes (i : Fin 5) :
    firstRectangleNodes P p q false (rawOuterFace.toOrderHom i) =
      firstTransport P p q
        (CoefficientLaurentUnitTenNodes.nodes P p (unitLowerFace.toOrderHom i)) :=
  congrArg (firstTransport P p q) (outer_nodes P p i)

/-- All five shifted first references use the actual right-whiskered source-unit square. -/
theorem first_upper_nodes (i : Fin 5) :
    firstRectangleNodes P p q true (rawOuterFace.toOrderHom i) =
      firstTransport P p q
        (CoefficientLaurentUnitTenNodes.nodes P p (unitShiftedFace.toOrderHom i)) := by
  change anchorNode (commonUnit P p q)
    (firstTransport P p q (BassH0Diagram.nodes P p (rawOuterFace.toOrderHom i))) = _
  rw [outer_nodes]
  exact (first_shift P p q _).trans
    (congrArg (firstTransport P p q) (five_shift P p i))

/-- All five ordinary middle references retain the original coefficient-p precomposition. -/
theorem middle_lower_nodes (i : Fin 5) :
    middleRectangleNodes P p q false (rawOuterFace.toOrderHom i) =
      middleTransport P p q
        (CoefficientLaurentUnitTenNodes.nodes P q (unitLowerFace.toOrderHom i)) :=
  congrArg (middleTransport P p q) (outer_nodes P q i)

/-- All five shifted middle references use the actual left-whiskered source-unit square. -/
theorem middle_upper_nodes (i : Fin 5) :
    middleRectangleNodes P p q true (rawOuterFace.toOrderHom i) =
      middleTransport P p q
        (CoefficientLaurentUnitTenNodes.nodes P q (unitShiftedFace.toOrderHom i)) := by
  change anchorNode (commonUnit P p q)
    (middleTransport P p q (BassH0Diagram.nodes P q (rawOuterFace.toOrderHom i))) = _
  rw [outer_nodes]
  exact (middle_shift P p q _).trans
    (congrArg (middleTransport P p q) (five_shift P q i))

/-- The complete ordinary first Laurent word is the transported original lower unit word. -/
theorem first_lower_parameter (s : I) :
    parameter (laurentReference P p q) (firstRectangleNodes P p q false)
      (ProjectionRectangleParameters.T BassH0Diagram.plusFace s) =
      mapParameter (firstTransport P p q)
        (parameter (CoefficientLaurentUnitTenNodes.source P p)
          (CoefficientLaurentUnitTenNodes.nodes P p)
          ((CoefficientLaurentUnitTenNodes.C0.symm.trans
            CoefficientLaurentUnitTenNodes.D0) s)) := by
  rw [mapParameter_parameter, ← raw_outer_word, ← unit_lower_word]
  change parameter (laurentReference P p q) (firstRectangleNodes P p q false)
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (laurentReference P p q)
      (fun i ↦ firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p i))
      (StdSimplex.map unitLowerFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (outerWord s))
    (funext (first_lower_nodes P p q))

/-- The complete shifted first word retains its own five references and original clocks. -/
theorem first_upper_parameter (s : I) :
    parameter (laurentReference P p q) (firstRectangleNodes P p q true)
      (ProjectionRectangleParameters.T BassH0Diagram.plusFace s) =
      mapParameter (firstTransport P p q)
        (parameter (CoefficientLaurentUnitTenNodes.source P p)
          (CoefficientLaurentUnitTenNodes.nodes P p)
          ((CoefficientLaurentUnitTenNodes.C1.symm.trans
            CoefficientLaurentUnitTenNodes.D1) s)) := by
  rw [mapParameter_parameter, ← raw_outer_word, ← shifted_word]
  change parameter (laurentReference P p q) (firstRectangleNodes P p q true)
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (laurentReference P p q)
      (fun i ↦ firstTransport P p q (CoefficientLaurentUnitTenNodes.nodes P p i))
      (StdSimplex.map unitShiftedFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (outerWord s))
    (funext (first_upper_nodes P p q))

/-- The complete ordinary middle Laurent word is the actual precomposed lower unit word. -/
theorem middle_lower_parameter (s : I) :
    parameter (laurentReference P p q) (middleRectangleNodes P p q false)
      (ProjectionRectangleParameters.T BassH0Diagram.plusFace s) =
      mapParameter (middleTransport P p q)
        (parameter (CoefficientLaurentUnitTenNodes.source P q)
          (CoefficientLaurentUnitTenNodes.nodes P q)
          ((CoefficientLaurentUnitTenNodes.C0.symm.trans
            CoefficientLaurentUnitTenNodes.D0) s)) := by
  rw [mapParameter_parameter, ← raw_outer_word, ← unit_lower_word]
  change parameter (laurentReference P p q) (middleRectangleNodes P p q false)
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (laurentReference P p q)
      (fun i ↦ middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q i))
      (StdSimplex.map unitLowerFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (outerWord s))
    (funext (middle_lower_nodes P p q))

/-- The complete shifted middle word retains the specified commonUnit and original clocks. -/
theorem middle_upper_parameter (s : I) :
    parameter (laurentReference P p q) (middleRectangleNodes P p q true)
      (ProjectionRectangleParameters.T BassH0Diagram.plusFace s) =
      mapParameter (middleTransport P p q)
        (parameter (CoefficientLaurentUnitTenNodes.source P q)
          (CoefficientLaurentUnitTenNodes.nodes P q)
          ((CoefficientLaurentUnitTenNodes.C1.symm.trans
            CoefficientLaurentUnitTenNodes.D1) s)) := by
  rw [mapParameter_parameter, ← raw_outer_word, ← shifted_word]
  change parameter (laurentReference P p q) (middleRectangleNodes P p q true)
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (laurentReference P p q)
      (fun i ↦ middleTransport P p q (CoefficientLaurentUnitTenNodes.nodes P q i))
      (StdSimplex.map unitShiftedFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (outerWord s))
    (funext (middle_upper_nodes P p q))

/-- The original entire p TenNodes characteristic map with its actual first transport. -/
def firstUnitMap : C(StdSimplex ℝ (Fin 10), Carrier P p q) :=
  (includeLaurent P p q).comp
    ((mapParameter (firstTransport P p q)).comp
      (parameter (CoefficientLaurentUnitTenNodes.source P p)
        (CoefficientLaurentUnitTenNodes.nodes P p)))

/-- The original entire q TenNodes characteristic map with its actual middle transport. -/
def middleUnitMap : C(StdSimplex ℝ (Fin 10), Carrier P p q) :=
  (includeLaurent P p q).comp
    ((mapParameter (middleTransport P p q)).comp
      (parameter (CoefficientLaurentUnitTenNodes.source P q)
        (CoefficientLaurentUnitTenNodes.nodes P q)))

abbrev firstOldUnitRaw := CoefficientLaurentUnitTenNodes.V.map (firstUnitMap P p q).continuous
abbrev firstNewUnitRaw := CoefficientLaurentUnitTenNodes.W.map (firstUnitMap P p q).continuous
abbrev firstLower :=
  (CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0).map
    (firstUnitMap P p q).continuous
abbrev firstUpper :=
  (CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1).map
    (firstUnitMap P p q).continuous

/-- Map the literal original first unit parameter, without changing any of its five stages. -/
def firstUnitComparisonRaw : ((firstOldUnitRaw P p q).trans (firstUpper P p q)).Homotopy
    ((firstLower P p q).trans (firstNewUnitRaw P p q)) :=
  (CoefficientLaurentUnitPastingLift.parameter.map (firstUnitMap P p q)).cast
    (by simp only [Path.map_trans]) (by simp only [Path.map_trans])

abbrev middleOldUnitRaw := CoefficientLaurentUnitTenNodes.V.map (middleUnitMap P p q).continuous
abbrev middleNewUnitRaw := CoefficientLaurentUnitTenNodes.W.map (middleUnitMap P p q).continuous
abbrev middleLower :=
  (CoefficientLaurentUnitTenNodes.C0.symm.trans CoefficientLaurentUnitTenNodes.D0).map
    (middleUnitMap P p q).continuous
abbrev middleUpper :=
  (CoefficientLaurentUnitTenNodes.C1.symm.trans CoefficientLaurentUnitTenNodes.D1).map
    (middleUnitMap P p q).continuous

/-- Map the literal original middle unit parameter, retaining the same internal rotation. -/
def middleUnitComparisonRaw : ((middleOldUnitRaw P p q).trans (middleUpper P p q)).Homotopy
    ((middleLower P p q).trans (middleNewUnitRaw P p q)) :=
  (CoefficientLaurentUnitPastingLift.parameter.map (middleUnitMap P p q)).cast
    (by simp only [Path.map_trans]) (by simp only [Path.map_trans])

/-- The first ordinary Laurent rail agrees as a complete carrier path at unchanged time. -/
theorem first_lower_rail (s : I) :
    firstLower P p q s = firstLaurentMovement P p q false s :=
  congrArg (includeLaurent P p q) (first_lower_parameter P p q s).symm

/-- The first shifted Laurent rail retains its complete commonUnit references. -/
theorem first_upper_rail (s : I) :
    firstUpper P p q s = firstLaurentMovement P p q true s :=
  congrArg (includeLaurent P p q) (first_upper_parameter P p q s).symm

/-- The middle ordinary Laurent rail agrees before any native evaluation. -/
theorem middle_lower_rail (s : I) :
    middleLower P p q s = middleLaurentMovement P p q false s :=
  congrArg (includeLaurent P p q) (middle_lower_parameter P p q s).symm

/-- The middle shifted Laurent rail is the whole original upper unit boundary. -/
theorem middle_upper_rail (s : I) :
    middleUpper P p q s = middleLaurentMovement P p q true s :=
  congrArg (includeLaurent P p q) (middle_upper_parameter P p q s).symm

/-- The actual first old unit joins the two rectangle movement sources. -/
abbrev firstOldUnit := Path.RetypedUnitComparison.oldUnit
  (firstOldUnitRaw P p q) (firstLower P p q) (firstUpper P p q)
  (firstLaurentMovement P p q false) (firstLaurentMovement P p q true)
  (first_lower_rail P p q) (first_upper_rail P p q)

/-- The actual first new unit joins the two rectangle movement targets. -/
abbrev firstNewUnit := Path.RetypedUnitComparison.newUnit
  (firstNewUnitRaw P p q) (firstLower P p q) (firstUpper P p q)
  (firstLaurentMovement P p q false) (firstLaurentMovement P p q true)
  (first_lower_rail P p q) (first_upper_rail P p q)

/-- The first entire unit comparison is typed using the two proved whole Laurent rails. -/
def firstUnitComparison :
    ((firstOldUnit P p q).trans (firstLaurentMovement P p q true)).Homotopy
      ((firstLaurentMovement P p q false).trans (firstNewUnit P p q)) :=
  Path.RetypedUnitComparison.comparison
    (firstOldUnitRaw P p q) (firstNewUnitRaw P p q)
    (firstLower P p q) (firstUpper P p q)
    (firstLaurentMovement P p q false) (firstLaurentMovement P p q true)
    (first_lower_rail P p q) (first_upper_rail P p q) (firstUnitComparisonRaw P p q)

/-- The actual middle old unit retains the two distinct rectangle movement sources. -/
abbrev middleOldUnit := Path.RetypedUnitComparison.oldUnit
  (middleOldUnitRaw P p q) (middleLower P p q) (middleUpper P p q)
  (middleLaurentMovement P p q false) (middleLaurentMovement P p q true)
  (middle_lower_rail P p q) (middle_upper_rail P p q)

/-- The actual middle new unit retains the two distinct rectangle movement targets. -/
abbrev middleNewUnit := Path.RetypedUnitComparison.newUnit
  (middleNewUnitRaw P p q) (middleLower P p q) (middleUpper P p q)
  (middleLaurentMovement P p q false) (middleLaurentMovement P p q true)
  (middle_lower_rail P p q) (middle_upper_rail P p q)

/-- The middle comparison uses exactly the selected original movement rails. -/
def middleUnitComparison :
    ((middleOldUnit P p q).trans (middleLaurentMovement P p q true)).Homotopy
      ((middleLaurentMovement P p q false).trans (middleNewUnit P p q)) :=
  Path.RetypedUnitComparison.comparison
    (middleOldUnitRaw P p q) (middleNewUnitRaw P p q)
    (middleLower P p q) (middleUpper P p q)
    (middleLaurentMovement P p q false) (middleLaurentMovement P p q true)
    (middle_lower_rail P p q) (middle_upper_rail P p q) (middleUnitComparisonRaw P p q)

/-- Retyping leaves the entire first old unit unchanged. -/
theorem firstOldUnit_apply (s : I) : firstOldUnit P p q s =
    firstUnitMap P p q (CoefficientLaurentUnitTenNodes.V s) := rfl

/-- Retyping leaves the entire first new unit unchanged. -/
theorem firstNewUnit_apply (s : I) : firstNewUnit P p q s =
    firstUnitMap P p q (CoefficientLaurentUnitTenNodes.W s) := rfl

/-- Retyping leaves the entire middle old unit unchanged. -/
theorem middleOldUnit_apply (s : I) : middleOldUnit P p q s =
    middleUnitMap P p q (CoefficientLaurentUnitTenNodes.V s) := rfl

/-- Retyping leaves the entire middle new unit unchanged. -/
theorem middleNewUnit_apply (s : I) : middleNewUnit P p q s =
    middleUnitMap P p q (CoefficientLaurentUnitTenNodes.W s) := rfl

/-- The first original unit parameter retains both of its independent times. -/
theorem firstUnitComparison_apply (r s : I) : firstUnitComparison P p q (r, s) =
    firstUnitMap P p q (CoefficientLaurentUnitPastingLift.parameter (r, s)) := rfl

/-- The middle original unit parameter retains both of its independent times. -/
theorem middleUnitComparison_apply (r s : I) : middleUnitComparison P p q (r, s) =
    middleUnitMap P p q (CoefficientLaurentUnitPastingLift.parameter (r, s)) := rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitPasting
