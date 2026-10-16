/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackNull
public import QuillenTest.ScalarUnitTrack
public import QuillenTest.ScalarUnitTrackTransport

/-! Literal reversed-first canonical null, level-zero path and its independent structure time. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace QuillenTest.ScalarUnitTrackNull
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Even at level zero the first half is precisely the reversed old comparison. -/
theorem original_zero_first_half
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space 0)
    (t : unitInterval) :
    ((perfectOpenFlatCanonicalFiberMap j).map 0 x).1.2
        ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ =
      (perfectOpenOriginalRestrictionFlatHomotopy j).level 0
        (unitInterval.symm t, (acyclicInclusionPrespectrumMap (perfectOpenNested j)).map 0 x) :=
  perfectOpenFlatCanonicalFiberMap_first_half j 0 x t

/-- Every original null time survives in the second half at every original level. -/
theorem original_null_second_half (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space n)
    (t : unitInterval) :
    ((perfectOpenFlatCanonicalFiberMap j).map n x).1.2
        ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ =
      (perfectOpenScalarRestrictionMap j).map n
        ((acyclicPrespectrumNullhomotopy (perfectOpenNested j)).level n (t, x)) :=
  perfectOpenFlatCanonicalFiberMap_second_half j n x t

/-- The original acyclic null is retained while rebase transport respects independent structure. -/
theorem original_null_structure_time (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (acyclicStructure (perfectOpenNested j))).space n) :
    (perfectOpenNormalizedAcyclicNullHomotopy j).level (n + 1)
        (s, (originalPrespectrum (acyclicStructure (perfectOpenNested j))).structureMap n x t) =
      (originalPrespectrum (perfectOpenWeakWaldhausen j)).structureMap n
        ((perfectOpenNormalizedAcyclicNullHomotopy j).level n (s, x)) t :=
  (perfectOpenNormalizedAcyclicNullHomotopy j).comm n s x t

end QuillenTest.ScalarUnitTrackNull
