/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialEvaluationConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportEvaluationClasses
public import Quillen.Waldhausen.Fibration.StableConnectingComparison

/-!
# The original geometric sign in initial coefficient localization

The intrinsic initial coefficient connecting map, evaluated by the actual
supported-to-acyclic Model map, is the negative of the unchanged geometric
Waldhausen boundary class. The original coefficient evaluation and degree cast
are kept explicitly; this does not yet identify a Bass telescope endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

private theorem stableMap_degree_cast {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    {d e : ℤ} (h : d = e) :
    eqToHom (congrArg (stableHomotopyGroup E) h) ≫ (stableHomotopyFunctor e).map f =
      (stableHomotopyFunctor d).map f ≫ eqToHom (congrArg (stableHomotopyGroup F) h) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Original evaluation detects the actual negative sign of the initial geometric boundary. -/
theorem boundedFlatCoefficientInitialConnecting_original_sign (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientOpenModel f a).waldhausen.K (n + 1)) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (supportAcyclicEvaluationModelMap f a))
        (stableFiberLiftConnecting
          ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
          ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
          ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) (n : ℤ)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
            (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1)
              (Additive.ofMul x)))) =
      -(originalKStableEquiv (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) n
        (Additive.ofMul (changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
          (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n
          (boundedFlatCoefficientOpenKEquiv f a (n + 1) x)))) := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  let := boundedFlatCoefficientGeometricFiberLift_isStableEquivalence f a (n : ℤ)
  have he := ConcreteCategory.congr_hom
    (boundedFlatCoefficientInitialConnecting_evaluation f a (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup
      ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
      (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1) (Additive.ofMul x)))
  have hc := ConcreteCategory.congr_hom
    (stableMap_degree_cast (prespectrumMap (coarseOriginalEvaluationModelMap f a)) κ)
    (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1) (Additive.ofMul x))
  have hk := coarseOriginalEvaluationModelMap_stable f a (n + 1) x
  have ht := hc.trans (congrArg
    (eqToHom (congrArg (stableHomotopyGroup
      (originalPrespectrum (boundedFlatPerfectOpenWaldhausen (schemeMap f a)))) κ)) hk)
  exact he.trans ((congrArg
    (stableFiberLiftConnecting
      (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
      (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a))) (n : ℤ))
    ht).trans (originalKStableEquiv_liftConnecting_sign _
      (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n κ
      (boundedFlatCoefficientOpenKEquiv f a (n + 1) x)))

end Quillen.PerfectComplexes
