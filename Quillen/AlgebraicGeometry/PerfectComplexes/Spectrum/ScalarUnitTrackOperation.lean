/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackTransport
public import Quillen.Topology.Prespectrum.SelfTrackIntertwining
public import Quillen.Topology.Prespectrum.SelfTrackStableNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationIntertwining
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationNaturality

/-!
# Original scalar restriction and flat-unit operations

The proved whole intertwining along the actual raw comparison Z, and separately along the
normalized comparison A, identifies the original finite and integer-graded operations. The
actual restriction map, every finite input, alternating sign and canonical reindexing are kept.
The unchanged canonical-null transport is constructed independently in `ScalarUnitTrackNull`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual raw comparison transports every finite input, including Pi-one at level zero. -/
theorem perfectOpenScalarOriginalOperation_restrict (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) ((originalPrespectrum (perfectWaldhausen X)).space n)
      ((originalPrespectrum (perfectWaldhausen X)).point n)) :
    piMap (m + 1) ((perfectOpenScalarRestrictionMap j).map n)
        ((perfectOpenScalarRestrictionMap j).map_point n)
        ((perfectOpenScalarOriginalHomotopy j r q hq).homotopyClassOperation n m a) =
      (perfectFlatUnitHomotopy j q).homotopyClassOperation n m a := by
  rw [← Homotopy.homotopyClassOperation_postcomp]
  exact ((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).homotopyClassOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
      (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) n m a

/-- The separately normalized scalar track uses its original reversed-first comparison A. -/
theorem perfectOpenScalarOperation_restrict (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) ((originalPrespectrum (perfectWaldhausen X)).space n)
      ((originalPrespectrum (perfectWaldhausen X)).point n)) :
    piMap (m + 1) ((perfectOpenScalarRestrictionMap j).map n)
        ((perfectOpenScalarRestrictionMap j).map_point n)
        ((perfectOpenScalarPrespectrumHomotopy j r q hq).homotopyClassOperation n m a) =
      (perfectFlatUnitHomotopy j q).homotopyClassOperation n m a := by
  rw [← Homotopy.homotopyClassOperation_postcomp]
  exact ((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).homotopyClassOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
      (perfectOpenScalarRestrictionUnitTrack j r q hq) n m a

/-- The raw stage keeps the exact alternating sign, integer degree and canonical tail offset. -/
theorem perfectOpenScalarOriginalCorrectedStage_restrict (d : ℤ) (n : ℕ) :
    ((-1 : ℤ) ^ n • (perfectOpenScalarOriginalHomotopy j r q hq).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectOpenWeakWaldhausen j)) d n).hom ≫
          (stableSystemMap (perfectOpenScalarRestrictionMap j) (d + 1)).app
            (parameterStableOffset d + n) =
      ((-1 : ℤ) ^ n • (perfectFlatUnitHomotopy j q).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectWaldhausen U)) d n).hom := by
  exact ((perfectOpenScalarOriginalHomotopy j r q hq).correctedStableStageOperation_postcomp
    (perfectOpenScalarRestrictionMap j) d n).symm.trans
      (congrArg (fun k => ((-1 : ℤ) ^ n • k) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectWaldhausen U)) d n).hom)
        (((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
          (perfectOpenScalarRestrictionMap j)).stableStageOperation_intertwine
            (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
            (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) d n))

/-- The normalized stage retains the same sign and tail through its distinct actual comparison. -/
theorem perfectOpenScalarCorrectedStage_restrict (d : ℤ) (n : ℕ) :
    ((-1 : ℤ) ^ n • (perfectOpenScalarPrespectrumHomotopy j r q hq).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectOpenWeakWaldhausen j)) d n).hom ≫
          (stableSystemMap (perfectOpenScalarRestrictionMap j) (d + 1)).app
            (parameterStableOffset d + n) =
      ((-1 : ℤ) ^ n • (perfectFlatUnitHomotopy j q).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectWaldhausen U)) d n).hom := by
  exact ((perfectOpenScalarPrespectrumHomotopy j r q hq).correctedStableStageOperation_postcomp
    (perfectOpenScalarRestrictionMap j) d n).symm.trans
      (congrArg (fun k => ((-1 : ℤ) ^ n • k) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectWaldhausen U)) d n).hom)
        (((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
          (perfectOpenScalarRestrictionMap j)).stableStageOperation_intertwine
            (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
            (perfectOpenScalarRestrictionUnitTrack j r q hq) d n))

/-- The raw scalar operation restricts to the actual flat-unit operation in every integer degree. -/
theorem perfectOpenScalarOriginalStableOperation_restrict (d : ℤ) :
    (perfectOpenScalarOriginalHomotopy j r q hq).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map (perfectOpenScalarRestrictionMap j) =
      (perfectFlatUnitHomotopy j q).stableOperation d := by
  rw [← Homotopy.stableOperation_postcomp]
  exact ((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).stableOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
      (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) d

/-- The normalized scalar operation has its own comparison in every integer degree. -/
theorem perfectOpenScalarStableOperation_restrict (d : ℤ) :
    (perfectOpenScalarPrespectrumHomotopy j r q hq).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map (perfectOpenScalarRestrictionMap j) =
      (perfectFlatUnitHomotopy j q).stableOperation d := by
  rw [← Homotopy.stableOperation_postcomp]
  exact ((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).stableOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
      (perfectOpenScalarRestrictionUnitTrack j r q hq) d

/-- The raw scalar K-operation restricts to the original unit operation, including K-zero. -/
theorem perfectOpenScalarOriginalKOperation_restrict (n : ℕ) :
    (KMap (perfectOpenRestrict_waldhausenExact j) (n + 1)).comp
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarOriginalHomotopy j r q hq) n) =
      originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n := by
  rw [← originalKSelfTrackOperation_postcomp]
  exact originalKSelfTrackOperation_intertwine (perfectWaldhausen X) (perfectWaldhausen U)
    ((perfectOpenScalarOriginalHomotopy j r q hq).postcomp (perfectOpenScalarRestrictionMap j))
    (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
    (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) n

/-- The normalized scalar K-operation retains its separate comparison on every original K-group. -/
theorem perfectOpenScalarKOperation_restrict (n : ℕ) :
    (KMap (perfectOpenRestrict_waldhausenExact j) (n + 1)).comp
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarPrespectrumHomotopy j r q hq) n) =
      originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n := by
  rw [← originalKSelfTrackOperation_postcomp]
  exact originalKSelfTrackOperation_intertwine (perfectWaldhausen X) (perfectWaldhausen U)
    ((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j))
    (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
    (perfectOpenScalarRestrictionUnitTrack j r q hq) n

end Quillen.PerfectComplexes
