/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Cofinality.EndotransformationHomotopy
public import Quillen.Topology.Prespectrum.StableExactness

/-! Original normalized scalar tracks, their independent structure coordinate, and the
prescribed null-conjugated loop map in the actual grading-coarse model. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace QuillenTest.GradingEndotransformation

open Quillen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Quillen.Waldhausen.Structure C) {V : Quillen.Waldhausen.Structure D}
  {G : Type w} [AddCommGroup G] (d : Quillen.Waldhausen.Cofinality.Grading V G)
  {F : C ⥤ D}
  (hF : Quillen.Waldhausen.IsExact W.cof W.weq
    d.coarseStructure.cof d.coarseStructure.weq F) (e : F ≅ F)

/-- The contraction begins at the unchanged original normalized scalar-isomorphism track. -/
theorem original_scalar_track (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationContraction W hF e.hom).level n (0, (s, x)) =
      (exactOriginalPrespectrumIsoHomotopy W d.coarseStructure hF hF e).level n (s, x) :=
  (d.exactEndotransformationContraction W hF e.hom).level n |>.apply_zero (s, x)

/-- Comparison time, scalar time, and the original structure-loop time remain independent. -/
theorem original_three_times (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum W).space n) :
    (d.exactEndotransformationContraction W hF e.hom).level (n + 1)
        (r, (s, (originalPrespectrum W).structureMap n x t)) =
      (originalPrespectrum d.coarseStructure).structureMap n
        ((d.exactEndotransformationContraction W hF e.hom).level n (r, (s, x))) t :=
  (d.exactEndotransformationContraction W hF e.hom).comm n r s x t

variable {T : LoopPrespectrum.{max u v}}
  (j : originalPrespectrum d.coarseStructure ⟶ T)
  (N : Homotopy (exactOriginalPrespectrumMap W d.coarseStructure hF ≫ j)
    (zeroHom (originalPrespectrum W) T))

/-- At the initial comparison face the actual loop still has both prescribed N legs. -/
theorem original_null_conjugate (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum W).space n) :
    Path.toContinuousMap
        ((d.exactEndotransformationNullLoopHomotopy W hF e.hom j N).level n (0, x)) s =
      (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF e.hom
        (fun _ ↦ rfl)).postcomp j).conjugateToZero N).level n (s, x) := by
  rw [(d.exactEndotransformationNullLoopHomotopy W hF e.hom j N).at_zero]
  rfl

/-- This actual global contraction kills the original loop map in every signed degree. -/
theorem original_signed_map_zero (k : ℤ) :
    (stableHomotopyFunctor k).map
      (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF e.hom
        (fun _ ↦ rfl)).postcomp j).nullLoopMap N) = 0 := by
  rw [(d.exactEndotransformationNullLoopHomotopy W hF e.hom j N).stableHomotopyMap_eq k,
    stableHomotopyMap_zero]

end QuillenTest.GradingEndotransformation
