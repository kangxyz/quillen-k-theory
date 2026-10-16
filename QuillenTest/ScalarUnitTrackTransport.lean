/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackTransport

/-! Raw whole scalar-cylinder transport, level zero and independent structure time. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace QuillenTest.ScalarUnitTrackTransport
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- Arbitrary original cubes keep the old scalar cylinder and the original track time. -/
theorem original_cube (m : ℕ) (p : GenLoop (Fin (m + 1))
    (perfectWaldhausen X).Delooping (perfectWaldhausen X).kBasepoint)
    (s : unitInterval) (z : Fin (m + 1) → unitInterval) :
    (perfectOpenScalarOriginalHomotopy j r q hq).level 1
        (s, (perfectWaldhausen X).smallModelDeloopingHomeomorph (p z)) =
      (perfectOpenWeakWaldhausen j).smallModelDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy (perfectWaldhausen X)
          (perfectOpenWeakWaldhausen j) (changeWeak_exact (perfectOpenNested j))
          (changeWeak_exact (perfectOpenNested j)) (perfectGlobalScalar X r)
          (perfectGlobalScalar_openWeak j r q hq) (s, p z)) :=
  perfectOpenScalarOriginalHomotopy_level_one j r q hq s (p z)

/-- The whole level-zero basepoint line is fixed throughout the actual two-parameter comparison. -/
theorem original_zero_basepoint (a s : unitInterval) :
    (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq).level 0
        (a, (s, (originalPrespectrum (perfectWaldhausen X)).point 0)) =
      (originalPrespectrum (perfectWaldhausen U)).point 0 := by
  rw [((perfectOpenScalarOriginalRestrictionUnitTrack j r q hq).level 0).eq_fst a
    (Or.inr (Or.inr rfl))]
  exact (((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).trans
      (perfectOpenOriginalRestrictionFlatHomotopy j)).at_point 0 s

/-- Comparison, original scalar, and structure coordinates remain independent at all levels. -/
theorem original_structure_time (n : ℕ) (a s t : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen X)).space n) :
    (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq).level (n + 1)
        (a, (s, (originalPrespectrum (perfectWaldhausen X)).structureMap n x t)) =
      (originalPrespectrum (perfectWaldhausen U)).structureMap n
        ((perfectOpenScalarOriginalRestrictionUnitTrack j r q hq).level n (a, (s, x))) t :=
  (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq).comm n a s x t

end QuillenTest.ScalarUnitTrackTransport
