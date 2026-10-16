/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficit
public import Quillen.Waldhausen.GrothendieckComparison.ImageQuotientCone

/-!
# The original perfect open deficit maps to its actual quotient grading

The target retains all perfect complexes on the open, changing only weak equivalences to
equality of their original image-quotient grades. The actual original deficit cone descends
without a shift through the specified zero-to-normalized-restriction track. These maps exist
for every open immersion; no stable equivalence or inherited Laurent seed square is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The literal quotient by the original relative-open restriction's algebraic image. -/
def perfectOpenDeficitGrading : Cofinality.Grading (perfectWaldhausen U)
    (ImageQuotient (perfectOpenWeakWaldhausen j) (perfectRestrict j)
      (perfectOpenRestrict_waldhausenExact j)) :=
  imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectRestrict j)
    (perfectOpenRestrict_waldhausenExact j)

/-- The unshifted original S-prespectrum of the actual quotient-grade weak structure. -/
def perfectOpenDeficitGradedPrespectrum : LoopPrespectrum :=
  originalPrespectrum (perfectOpenDeficitGrading j).coarseStructure

/-- The original change of weaknesses on perfect complexes on the open. -/
def perfectOpenDeficitGradingChangeWeak :
    originalPrespectrum (perfectWaldhausen U) ⟶ perfectOpenDeficitGradedPrespectrum j :=
  Fibration.changeWeakPrespectrumMap (perfectOpenDeficitGrading j).nested

/-- The specified reversed zero-to-normalized-restriction track, with its original endpoints. -/
def perfectOpenDeficitGradingNullhomotopy : LoopPrespectrum.Homotopy
    (perfectOpenRestrictPrespectrumMap j ≫ perfectOpenDeficitGradingChangeWeak j)
    (zeroHom (originalPrespectrum (perfectOpenWeakWaldhausen j))
      (perfectOpenDeficitGradedPrespectrum j)) :=
  imageQuotientPrespectrumNullhomotopy (perfectOpenWeakWaldhausen j) (perfectRestrict j)
    (perfectOpenRestrict_waldhausenExact j)

/-- The actual deficit cone maps to the genuine unshifted graded-coarse target. -/
def perfectOpenDeficitGradingMap :
    perfectOpenDeficit j ⟶ perfectOpenDeficitGradedPrespectrum j :=
  imageQuotientConeMap (perfectOpenWeakWaldhausen j) (perfectRestrict j)
    (perfectOpenRestrict_waldhausenExact j)

/-- The original inclusion face remains the unchanged original change-weak map. -/
@[reassoc]
theorem perfectOpenDeficitGradingMap_inclusion :
    mappingConeInclusion (perfectOpenRestrictPrespectrumMap j) ≫
      perfectOpenDeficitGradingMap j = perfectOpenDeficitGradingChangeWeak j :=
  imageQuotientConeMap_inclusion (perfectOpenWeakWaldhausen j) (perfectRestrict j)
    (perfectOpenRestrict_waldhausenExact j)

/-- Every original cone-cylinder point retains the prescribed original null track. -/
theorem perfectOpenDeficitGradingMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (perfectOpenWeakWaldhausen j)).space n) :
    (perfectOpenDeficitGradingMap j).map n
        (ReducedMappingCone.cylinder
          ((originalPrespectrum (perfectOpenWeakWaldhausen j)).point n)
          ((originalPrespectrum (perfectWaldhausen U)).point n)
          ((perfectOpenRestrictPrespectrumMap j).map n) (s, x)) =
      (perfectOpenDeficitGradingNullhomotopy j).level n (s, x) := rfl

end Quillen.PerfectComplexes
