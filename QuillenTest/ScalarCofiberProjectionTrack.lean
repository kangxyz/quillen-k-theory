/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberProjectionTrack

/-! Original all-level scalar triangle, fine projection endpoints and the whole change-weak path. -/
public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.Waldhausen.Additivity Quillen.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace QuillenTest.ScalarCofiberProjectionTrack
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- Level zero retains the entire actual inclusion/projection concatenation. -/
theorem original_zero_level (t : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen X)).space 0) :
    (perfectOpenScalarProjectionCompositionTrack j r q hq).level 0 (1, (t, x)) =
      ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).level 0 (t, x) :=
  ((perfectOpenScalarProjectionCompositionTrack j r q hq).level 0).apply_one (t, x)

/-- Structure time remains independent of the two original triangle times. -/
theorem original_independent_structure (n : ℕ) (a s t : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen X)).space n) :
    (perfectOpenScalarProjectionCompositionTrack j r q hq).level (n + 1)
        (a, (s, (originalPrespectrum (perfectWaldhausen X)).structureMap n x t)) =
      (originalPrespectrum (perfectOpenNested j).coarse).structureMap n
        ((perfectOpenScalarProjectionCompositionTrack j r q hq).level n (a, (s, x))) t :=
  (perfectOpenScalarProjectionCompositionTrack j r q hq).comm n a s x t

/-- The original fine projection is preserved at every time and coefficient input. -/
theorem original_fine_projection (t : unitInterval) (x : (perfectWaldhausen X).Delooping) :
    changeWeakMap (perfectOpenNested j)
        (perfectOpenScalarProjectionFineRealizationHomotopy j r (t, x)) =
      perfectOpenScalarProjectionRealizationHomotopy j r (t, x) :=
  perfectOpenScalarProjectionRealizationHomotopy_changeWeak j r t x

/-- The fine projection starts at exactly the same coarse-rebased middle functor. -/
theorem original_fine_projection_source (x : (perfectWaldhausen X).Delooping) :
    perfectOpenScalarProjectionFineRealizationHomotopy j r (0, x) =
      deloopingMap (perfectOpenScalarMiddleRebase_fineExact j r) x :=
  (perfectOpenScalarProjectionFineRealizationHomotopy j r).apply_zero x

/-- The fine projection ends at exactly the same coarse-rebased identity functor. -/
theorem original_fine_projection_target (x : (perfectWaldhausen X).Delooping) :
    perfectOpenScalarProjectionFineRealizationHomotopy j r (1, x) =
      deloopingMap (perfectOpenScalarIdentityRebase_fineExact j) x :=
  (perfectOpenScalarProjectionFineRealizationHomotopy j r).apply_one x

/-- The raw scalar keeps the entire actual normalization prefix and original triangle. -/
def original_raw_intertwining :
    ((perfectOpenScalarOriginalHomotopy j r q hq).trans
      (perfectOpenChangeWeakNormalizationHomotopy j)).RelHomotopy
      ((perfectOpenChangeWeakNormalizationHomotopy j).trans
        ((perfectOpenScalarInclusionHomotopy j r q hq).trans
          (perfectOpenScalarProjectionHomotopy j r))) :=
  perfectOpenScalarRawProjectionIntertwining j r q hq

end QuillenTest.ScalarCofiberProjectionTrack
