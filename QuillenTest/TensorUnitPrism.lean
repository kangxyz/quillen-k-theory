/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitPullbackPrism
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorLaurentUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportHomotopy
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitSingle
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-! Consumers of the actual tensor-unit edge, original zero/support, and whole relative prism. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.TensorUnitPrism

/-- The actual tensor action is conjugate to the original forward scalar as a whole natural map. -/
theorem action_conjugation {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom =
      (boundedFlatPerfectTensorUnitPullbackIso f).hom ≫
        (boundedFlatPerfectPullbackUnitIso f r).hom ≫
        (boundedFlatPerfectTensorUnitPullbackIso f).inv := by
  calc
    _ = ((boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
        (boundedFlatPerfectTensorUnitPullbackIso f).hom) ≫
        (boundedFlatPerfectTensorUnitPullbackIso f).inv := by simp [Category.assoc]
    _ = ((boundedFlatPerfectTensorUnitPullbackIso f).hom ≫
        (boundedFlatPerfectPullbackUnitIso f r).hom) ≫
        (boundedFlatPerfectTensorUnitPullbackIso f).inv := by
      rw [boundedFlatPerfectTensorUnitPullbackAutomorphism_unitor]
    _ = _ := Category.assoc _ _ _

/-- The selected coefficient really is the original structure-module automorphism on O[0]. -/
theorem original_unit_single (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    ((complexTensorUnitAutomorphism X r).hom ≫ (complexTensorUnitIso X).hom).app
        ((CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) =
      (tensorLeftSingleUnitIso X (SheafOfModules.unit X.ringCatSheaf) 0).hom ≫
        (CochainComplex.singleFunctor X.Modules 0).map (unitMul X r) :=
  complexTensorUnitAutomorphism_single X r 0

/-- Support after tensor is still actual acyclicity under the same original open restriction. -/
theorem tensor_open_acyclic {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : (boundedFlatPerfectSupported j).FullSubcategory) :
    ((restrict j).obj ((boundedFlatPerfectSupportedTensorUnit j).obj K).obj).Acyclic :=
  ((boundedFlatPerfectSupportedTensorUnit j).obj K).property.2

/-- Canceling the genuine unitor gives a comparison of the entire original tensor/scalar loops. -/
def wholeTensorBoundary {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectTensorUnitHomotopy f r).RelHomotopy
      (((boundedFlatPerfectTensorUnitUnitorHomotopy f).trans
        (boundedFlatPerfectUnitHomotopy f r)).trans
          (boundedFlatPerfectTensorUnitUnitorHomotopy f).symm) :=
  Homotopy.RelHomotopy.conjugateBoundary _ _ _ (boundedFlatPerfectTensorUnitUnitorPasting f r)

/-- The first comparison face retains the entire tensor track followed by its original unitor. -/
theorem whole_original_first_face {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
    (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (boundedFlatPerfectTensorUnitUnitorPasting f r).level n (0, (s, x)) =
      ((boundedFlatPerfectTensorUnitHomotopy f r).trans
        (boundedFlatPerfectTensorUnitUnitorHomotopy f)).level n (s, x) :=
  ((boundedFlatPerfectTensorUnitUnitorPasting f r).level n).apply_zero (s, x)

/-- Comparison time, coefficient-edge time and spectrum structure time stay independent. -/
theorem whole_original_structure_time {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
    (n : ℕ) (a s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (boundedFlatPerfectTensorUnitUnitorPasting f r).level (n + 1)
        (a, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).structureMap n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap n
        ((boundedFlatPerfectTensorUnitUnitorPasting f r).level n (a, (s, x))) t :=
  (boundedFlatPerfectTensorUnitUnitorPasting f r).comm n a s x t

/-- The supported coefficient edge still fixes the actual chosen zero before any rebasing. -/
theorem supported_original_zero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app
        (boundedFlatPerfectSupportedWaldhausen j).zero = 𝟙 _ :=
  boundedFlatPerfectSupportedTensorUnitAutomorphism_zero j r

end QuillenTest.TensorUnitPrism
