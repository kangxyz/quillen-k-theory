/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficitGrading

/-! Original restriction, cone face, cylinder and structure-coordinate consumers. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
universe u
namespace QuillenTest.OpenDeficitGrading

open Quillen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The cone face uses the unchanged original change of weaknesses, without choosing an inverse. -/
theorem original_inclusion_face (n : ℕ)
    (y : (originalPrespectrum (perfectWaldhausen U)).space n) :
    (perfectOpenDeficitGradingMap j).map n
        ((mappingConeInclusion (perfectOpenRestrictPrespectrumMap j)).map n y) =
      (perfectOpenDeficitGradingChangeWeak j).map n y :=
  congrArg (fun f => f.map n y) (perfectOpenDeficitGradingMap_inclusion j)

/-- The initial null face retains the original restriction followed by the original change map. -/
theorem original_null_initial (n : ℕ)
    (x : (originalPrespectrum (perfectOpenWeakWaldhausen j)).space n) :
    (perfectOpenDeficitGradingNullhomotopy j).level n (0, x) =
      (perfectOpenDeficitGradingChangeWeak j).map n
        ((perfectOpenRestrictPrespectrumMap j).map n x) :=
  (perfectOpenDeficitGradingNullhomotopy j).at_zero n x

/-- The entire original cone cylinder evaluates to the same prescribed track. -/
theorem original_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (perfectOpenWeakWaldhausen j)).space n) :
    (perfectOpenDeficitGradingMap j).map n
        (Quillen.ReducedMappingCone.cylinder
          ((originalPrespectrum (perfectOpenWeakWaldhausen j)).point n)
          ((originalPrespectrum (perfectWaldhausen U)).point n)
          ((perfectOpenRestrictPrespectrumMap j).map n) (s, x)) =
      (perfectOpenDeficitGradingNullhomotopy j).level n (s, x) :=
  perfectOpenDeficitGradingMap_cylinder j n s x

/-- Null-track time and the actual structure-loop coordinate are independent. -/
theorem original_structure_coordinate (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (perfectOpenWeakWaldhausen j)).space n) :
    (perfectOpenDeficitGradingNullhomotopy j).level (n + 1)
        (s, (originalPrespectrum (perfectOpenWeakWaldhausen j)).structureMap n x t) =
      (perfectOpenDeficitGradedPrespectrum j).structureMap n
        ((perfectOpenDeficitGradingNullhomotopy j).level n (s, x)) t :=
  (perfectOpenDeficitGradingNullhomotopy j).comm n s x t

end QuillenTest.OpenDeficitGrading
