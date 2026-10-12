/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedDiagramNull
public import Quillen.KTheory.Bass.StrictDiagramIterateNull
public import Quillen.Topology.Prespectrum.StableExactness

/-!
# The actual graded Bass transitions are null in every signed degree

The existing strict Bass iterate acts on the original coefficient-natural seed null. Its
identity target is removed only by the actual map-identity and composition-identity equations.
Left-recursive iteration makes the target literally the next original stage, so the resulting
whole nullhomotopy belongs to the unchanged strictDiagramTransition. Homotopy invariance then
makes each original transition map zero in every signed stable degree, without connectivity
or a newly chosen stage seed. This does not assert that any individual stage group vanishes.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The original iterated seed transition is null through the prescribed iterated diagram null. -/
def boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy (k : ℕ) (a : Under R) :
    LoopPrespectrum.Homotopy
      ((strictDiagramTransition (laurentUnderSquareFunctor R)
        (boundedFlatAffineFullOpenGradedSectionBassSeed j) k).app a)
      (zeroHom
        (((strictDiagramIterate (laurentUnderSquareFunctor R) k).obj
          (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)).obj a)
        (((strictDiagramIterate (laurentUnderSquareFunctor R) (k + 1)).obj
          (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)).obj a)) :=
  ((strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull j) k).homotopy a).cast
      (by
        let I := strictDiagramIterate (laurentUnderSquareFunctor R) k
        let P := (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)
        have hid : (I.map (𝟙 P)).app a = 𝟙 ((I.obj P).obj a) :=
          congrArg (fun η : I.obj P ⟶ I.obj P ↦ η.app a) (I.map_id P)
        exact (congrArg
          (fun g ↦ (I.map (boundedFlatAffineFullOpenGradedSectionBassSeed j)).app a ≫ g)
          hid).trans (Category.comp_id _)) rfl

/-- Removing the mapped identity changes no original iterate-null value or null coordinate. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy_level
    (k : ℕ) (a : Under R) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) k).obj
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j k a).level n (r, x) =
      ((strictDiagramIterateNull (laurentUnderSquareFunctor R)
        (boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull j) k).homotopy a).level n
          (r, x) := rfl

/-- The zero stage retains the original seed null, including its exact output-loop value. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy_zero_level
    (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j 0 a).level n (r, x) =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (r, x) := rfl

/-- Every unchanged graded transition induces zero on the original integer-graded stable groups. -/
theorem boundedFlatAffineFullOpenGradedSectionBassTransition_stableMap_eq_zero
    (k : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((strictDiagramTransition (laurentUnderSquareFunctor R)
        (boundedFlatAffineFullOpenGradedSectionBassSeed j) k).app a) = 0 :=
  ((boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j k a).stableHomotopyMap_eq
    d).trans (stableHomotopyMap_zero _ _ d)

end Quillen.PerfectComplexes
