/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedNullNaturality
public import Quillen.Topology.Prespectrum.DiagramNullHomotopy

/-!
# The original graded Bass seed null as a strict diagram null

The actual coefficient-natural seed null is bundled with the identity of the original Bass
output diagram. Only the source identity-composition witness is transported; every null-time
value remains the original prescribed loop-valued homotopy. No substitute null or localization
null is supplied as a hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The exact original graded seed null, with the identity of its actual Bass target diagram. -/
def boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull :
    DiagramNullHomotopy (boundedFlatAffineFullOpenGradedSectionBassSeed j)
      (𝟙 ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j))) where
  homotopy a := (boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).cast
    (by
      simp only [NatTrans.id_app, boundedFlatAffineFullOpenGradedSectionBassSeed_app]
      exact (Category.comp_id (boundedFlatAffineFullOpenGradedSectionBassSeedMap j a)).symm) rfl
  naturality f n r x := by
    change (parameterLoopingMap (boundedFlatAffineFullOpenGradedSectionBassConeMap j f)).map n
      ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j _).level n (r, x)) =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j _).level n
        (r, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x)
    exact boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy_naturality_apply j f n r x

/-- The identity endpoint cast changes neither the original null time nor its loop value. -/
theorem boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull_level
    (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull j).homotopy a).level n (r, x) =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (r, x) := rfl

end Quillen.PerfectComplexes
