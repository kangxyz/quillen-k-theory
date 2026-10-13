/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassSeed
public import Quillen.KTheory.Bass.StrictLaurentSeedContraction

/-!
# Actual whole contraction of the original global graded Laurent seed

The original zero endomorphism is weak because its two endpoint grades are
equal. This actual witness supplies the reusable Model-action contraction and
its coefficient-natural original seed null. The source-leg cylinder, both
independent times and original output-loop coordinate are unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

/-- The actual chosen-zero endomorphism has equal original quotient grades. -/
theorem boundedFlatCoefficientGradedLaurentZero_weak (a : Under R)
    (S : (boundedFlatCoefficientGradedOpenModelFunctor f).obj a) :
    ((boundedFlatCoefficientGradedOpenModelFunctor f).obj
      ((laurentUnderFunctor R).obj a)).waldhausen.weq
      ((modelZeroEndotransformation ((boundedFlatCoefficientGradedOpenModelFunctor f).map
        ((laurentUnderCoefficient R).app a))).app S) := rfl

/-- The whole original Laurent-action contraction has its same scalar and point endpoints. -/
def boundedFlatCoefficientGradedLaurentContraction (a : Under R) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).contraction
    (boundedFlatCoefficientGradedLaurentZero_weak f) a

/-- The same chosen contraction preserves both independent times under every coefficient map. -/
theorem boundedFlatCoefficientGradedLaurentContraction_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (r t : unitInterval)
    (x : ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).map
      ((laurentUnderFunctor R).map g)).map n
        ((boundedFlatCoefficientGradedLaurentContraction f a).level n (r, (t, x))) =
      (boundedFlatCoefficientGradedLaurentContraction f b).level n
        (r, (t, ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).map g).map n x)) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).contraction_naturality
    (boundedFlatCoefficientGradedLaurentZero_weak f) g n r t x

/-- The original graded seed is null through its prescribed original source-leg conjugation. -/
def boundedFlatCoefficientGradedOpenBassSeedNull (a : Under R) :
    LoopPrespectrum.Homotopy (boundedFlatCoefficientGradedOpenBassSeedMap f a)
      (zeroHom ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).obj a)
        (parameterLooping (boundedFlatCoefficientGradedOpenBassCone f a))) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).seedNullHomotopy
    (boundedFlatCoefficientGradedLaurentZero_weak f) a

/-- The whole original graded seed null is coefficient-natural, with its actual Bass target. -/
def boundedFlatCoefficientGradedOpenBassSeedDiagramNull :
    DiagramNullHomotopy (boundedFlatCoefficientGradedOpenBassSeed f)
      (𝟙 ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientGradedOpenPrespectrumFunctor f))) :=
  (boundedFlatCoefficientGradedOpenLaurentAction f).seedDiagramNull
    (boundedFlatCoefficientGradedLaurentZero_weak f)

/-- The endpoint cast retains the same original graded seed-null time and loop value. -/
theorem boundedFlatCoefficientGradedOpenBassSeedDiagramNull_level (a : Under R)
    (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatCoefficientGradedOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientGradedOpenBassSeedDiagramNull f).homotopy a).level n (r, x) =
      (boundedFlatCoefficientGradedOpenBassSeedNull f a).level n (r, x) := rfl

end Quillen.PerfectComplexes
