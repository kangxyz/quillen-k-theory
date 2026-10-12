/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionJointData
public import Quillen.Topology.Prespectrum.StableLevelOne
public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum

/-!
# Signed concentration of the actual full-open graded section prespectrum

The original positive graded K-groups identify with the nonnegative stable groups of the
unchanged section Model through its level-one Omega comparison. Its connected positive
levels also give negative vanishing. Thus its actual stable groups vanish in every nonzero
signed degree, without compactness or coefficient-flatness assumptions. No degree-zero
comparison or localization statement is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original positive graded K-group vanishing transfers to the same section prespectrum. -/
theorem boundedFlatAffineFullOpenGradedSection_stable_succ_subsingleton
    (a : Under R) (n : ℕ) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) ((n + 1 : ℕ) : ℤ)) := by
  let : Subsingleton ((boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) :=
    boundedFlatAffineFullOpenGradedSection_K_succ_subsingleton j a n
  let e : Additive ((boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) ≃+
      stableHomotopyGroup
        (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) ((n + 1 : ℕ) : ℤ) :=
    levelOneStableEquiv (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a))
      (prespectrum_isOmega (boundedFlatAffineFullOpenGradedSectionModel j a)) (n + 1)
  exact e.symm.injective.subsingleton

/-- Connected positive levels of the actual section Model give all negative stable vanishing. -/
theorem boundedFlatAffineFullOpenGradedSection_stable_neg_subsingleton
    (a : Under R) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) d) :=
  stableHomotopyGroup_subsingleton_of_neg
    (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a))
    (prespectrum_isOmega (boundedFlatAffineFullOpenGradedSectionModel j a))
    (fun n ↦ stageSpace_pathConnected n (boundedFlatAffineFullOpenGradedSectionModel j a)) d hd

/-- The original full-open graded section prespectrum has no nonzero-degree stable classes. -/
theorem boundedFlatAffineFullOpenGradedSection_stable_subsingleton
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) d) := by
  by_cases hn : d < 0
  · exact boundedFlatAffineFullOpenGradedSection_stable_neg_subsingleton j a d hn
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    rw [he, hp]
    exact boundedFlatAffineFullOpenGradedSection_stable_succ_subsingleton j a (d.toNat - 1)

end Quillen.PerfectComplexes
