/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionScalar
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap

/-! The actual Laurent summand of Raw1 retains its entire prescribed eighteen-node family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1LaurentNativeCell
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (laurentUnderFunctor R) a)))
local notation "d" => CategoryTheory.Functor.obj (laurentUnderFunctor R) b
local notation "F" => CoefficientBassLaurentProjectionScalar.reference P α f
local notation "p" => CoefficientBassLaurentProjectionScalar.family P α f
local notation "Y" => mappingCone (boundedFlatCoefficientBassSquareComparison P d)

/-- The Laurent input is arbitrary and both original comparison coordinates remain independent. -/
def family (n : ℕ) : C((I × I) × (prespectrum V).space n, (Y).space n) :=
  ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).map n).comp
    (compactPrespectrumFamily F p n)

/-- The full original finite parameter is evaluated without replacing its chosen interior. -/
theorem family_apply (n : ℕ) (z : I × I) (x : (prespectrum V).space n) :
    family P α f n (z, x) =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).map n
        (prespectrumFamily F (CoefficientBassLaurentProjectionScalar.nodes P α f) n
          (CoefficientBassLaurentProjectionScalar.scalarComparison z, x)) := by
  exact congrArg ((mappingConeInclusion
    (boundedFlatCoefficientBassSquareComparison P d)).map n)
      (compactPrespectrumFamily_eq_simplex F p
        (CoefficientBassLaurentProjectionScalar.nodes P α f) z
        (CoefficientBassLaurentProjectionScalar.scalarComparison z) rfl n x)

/-- The entire Laurent cell is based at every comparison parameter. -/
theorem family_point (n : ℕ) (z : I × I) :
    family P α f n (z, (prespectrum V).point n) = (Y).point n := by
  exact (congrArg ((mappingConeInclusion
    (boundedFlatCoefficientBassSquareComparison P d)).map n)
    (compactPrespectrumFamily_point F p n z)).trans
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).map_point n)

/-- Structure time is independent of both Laurent coherence coordinates. -/
theorem family_structure (n : ℕ) (z : I × I)
    (x : (prespectrum V).space n) (s : I) :
    family P α f (n + 1) (z, (prespectrum V).structureMap n x s) =
      (Y).structureMap n (family P α f n (z, x)) s := by
  exact (congrArg ((mappingConeInclusion
    (boundedFlatCoefficientBassSquareComparison P d)).map (n + 1))
    (compactPrespectrumFamily_structure F p n z x s)).trans
      (congrArg (fun q ↦ q s)
        ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P d)).comm n _))

end Quillen.PerfectComplexes.CoefficientBassRaw1LaurentNativeCell
