/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedPairNaturality
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedInputNull

/-! Actual supported input, pair restriction and original tensor-null regression. -/
noncomputable section
open CategoryTheory CategoryTheory.Functor MonoidalCategory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.PerfectComplexes
open scoped Simplicial
universe u

example {U X Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) (k : ℕ) :
    rowTransformationCylinder
        (F := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (G := tensorCoefficientSupportedForgetModel j ≫ tensorUnitPullbackModelMap f)
        (Functor.whiskerLeft (tensorCoefficientSupportedForgetModel j).functor
          (tensorUnitPullbackModelTransformation f r))
        (fun A => tensorUnitPullbackModelTransformation_weak f r
          ((tensorCoefficientSupportedForgetModel j).functor.obj A)) k =
      (((stages k).map (tensorCoefficientSupportedForgetModel j) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackCoefficientStageCylinder f r k :=
  tensorUnitSupportedCoefficientStageCylinder_eq f r j k

example {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ) :
    Functor.whiskerRight (tensorSupportedPairAutomorphism p r).hom
        (tensorCoefficientSupportedForget A.obj.hom) ≫ (tensorSupportedPairForgetIso p).hom =
      (tensorSupportedPairForgetIso p).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (boundedFlatPerfectTensorUnitPullbackAutomorphism p.hom.right r).hom :=
  tensorSupportedPairForget_unit p r

example {U X Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    ((tensorSupportedCompositeHomotopy j f r).trans
      (tensorSupportedInputNormalization j f)).RelHomotopy
      ((tensorSupportedInputNormalization j f).trans
        (Homotopy.precomp (tensorSupportedInputPrespectrumMap j)
          (boundedFlatPerfectTensorUnitHomotopy f r))) :=
  tensorSupportedInputNormalizationPasting j f r

example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
    {U : Scheme.{u}} (j : U ⟶ space (op P, a)) [IsOpenImmersion j]
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :
    Path.toContinuousMap
      ((tensorSupportedInputConeWordComparison P a j).zeroLoopMapHomotopy.level n (r, x)) s =
      (tensorSupportedInputConeWordComparison P a j).level n (r, (s, x)) :=
  tensorSupportedInputConeWordComparison_apply P a j n r s x

example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
    {U : Scheme.{u}} (j : U ⟶ space (op P, a)) [IsOpenImmersion j]
    (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :
    (tensorSupportedInputOriginalNull P a j).level n (s, x) =
      (boundedFlatCoefficientTensorConeNull P a).level n
        (s, (tensorSupportedInputPrespectrumMap j).map n x) := rfl
