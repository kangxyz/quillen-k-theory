/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryInitialClasses
public import Quillen.KTheory.Bass.SchemeInitialModelClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKStableComparison

/-! # Actual basic and auxiliary nonnegative initial Model classes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original nonnegative fiber Model class follows the actual row map and old inclusion. -/
theorem ParameterFullCurrentNull.current_fine_fiber_modelClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterModels.supported f.left).obj (specUnder.obj a)).waldhausen.K n) :
    (ParameterFullCurrentNull.currentFineSupportComparison f a (n : ℤ)).hom
        (currentModelClass (ParameterModels.supported f.left) (supportedTrack f.left)
          (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map ((boundedFlatCoefficientSupportedBassTelescopeInclusion
        f 0).app a)
        (modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) n
          (Additive.ofMul (Quillen.Waldhausen.KMap (((parameterSupportedRowIso f).hom ≫
            supportedRowRestriction f).app a).exact n x))) := by
  have h := ConcreteCategory.congr_hom
    (ParameterFullCurrentNull.current_fine_initial_fiber f a (n : ℤ))
    (modelKStableEquiv ((ParameterModels.supported f.left).obj (specUnder.obj a)) n
      (Additive.ofMul x))
  exact h.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map ((boundedFlatCoefficientSupportedBassTelescopeInclusion f
      0).app a))
    (modelKStableEquiv_naturality (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction
      f).app a) n x).symm)

omit [IsOpenImmersion f.left] in
/-- The original nonnegative open Model class follows the actual row map and old inclusion. -/
theorem ParameterFullCurrentNull.current_fine_open_modelClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterModels.ambient P.left).obj (specUnder.obj a)).waldhausen.K n) :
    (ParameterFullCurrentNull.currentFineOpenComparison f a (n : ℤ)).hom
        (currentModelClass (ParameterModels.ambient P.left) (ambientTrack P.left) (specUnder.obj
          a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map ((boundedFlatCoefficientAmbientBassTelescopeInclusion P
        0).app a)
        (modelKStableEquiv (boundedFlatCoefficientSectionModel (Opposite.op P, a)) n
          (Additive.ofMul (Quillen.Waldhausen.KMap ((parameterCoefficientRestriction P).app
            a).exact n x))) := by
  have h := ConcreteCategory.congr_hom
    (ParameterFullCurrentNull.current_fine_initial_open f a (n : ℤ))
    (modelKStableEquiv ((ParameterModels.ambient P.left).obj (specUnder.obj a)) n (Additive.ofMul
      x))
  exact h.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map ((boundedFlatCoefficientAmbientBassTelescopeInclusion P
      0).app a))
    (modelKStableEquiv_naturality ((parameterCoefficientRestriction P).app a) n x).symm)

/-- The original nonnegative fiber Model class follows the actual row map and old inclusion. -/
theorem ParameterAuxiliaryCurrentFiber.current_fine_fiber_modelClass (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a)).waldhausen.K n) :
    (ParameterAuxiliaryCurrentFiber.currentFineSupportComparison f T a (n : ℤ)).hom
        (currentModelClass (ParameterAuxiliarySupport.fiber f.left T)
          (ParameterAuxiliarySupport.fiberAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n
          (Additive.ofMul (Quillen.Waldhausen.KMap
            ((GlobalAuxiliaryParameterCoefficient.fiberComparison f T).app a).exact n x))) := by
  have h := ConcreteCategory.congr_hom
    (ParameterAuxiliaryCurrentFiber.current_fine_initial_fiber f T a (n : ℤ))
    (modelKStableEquiv ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a)) n
      (Additive.ofMul x))
  exact h.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a))
    (modelKStableEquiv_naturality ((GlobalAuxiliaryParameterCoefficient.fiberComparison f T).app
      a) n x).symm)

omit [IsOpenImmersion f.left] in
/-- The original nonnegative open Model class follows the actual row map and old inclusion. -/
theorem ParameterAuxiliaryCurrentFiber.current_fine_open_modelClass (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a)).waldhausen.K n) :
    (ParameterAuxiliaryCurrentFiber.currentFineOpenComparison f T a (n : ℤ)).hom
        (currentModelClass (ParameterAuxiliarySupport.openModel f.left T)
          (ParameterAuxiliarySupport.openAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
        (modelKStableEquiv (boundedFlatCoefficientSupportedFullOpenModel f T a) n
          (Additive.ofMul (Quillen.Waldhausen.KMap
            ((GlobalAuxiliaryParameterCoefficient.openComparison f T).app a).exact n x))) := by
  have h := ConcreteCategory.congr_hom
    (ParameterAuxiliaryCurrentFiber.current_fine_initial_open f T a (n : ℤ))
    (modelKStableEquiv ((ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a)) n
      (Additive.ofMul x))
  exact h.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a))
    (modelKStableEquiv_naturality ((GlobalAuxiliaryParameterCoefficient.openComparison f T).app a)
      n x).symm)

end Quillen.PerfectComplexes
