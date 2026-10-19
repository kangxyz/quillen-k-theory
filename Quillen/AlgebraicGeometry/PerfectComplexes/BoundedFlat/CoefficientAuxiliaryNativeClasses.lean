/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialConnectingSign
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryAcyclicEvaluation

/-!
# Original classes of the actual native auxiliary acyclic conversion

The literal intersection-support equivalence followed by AsSmall.up gives a
stable equivalence. It carries every original native K-class to the unchanged
acyclic K-class, retaining the actual functor and its selected zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual native acyclic conversion is a stable equivalence in every signed degree. -/
theorem auxiliaryNativeFiberAcyclicModelMap_isStableEquivalence (a : Under R) :
    IsStableEquivalence (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a)) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedFlatCoefficientSupportedFiberModel f T a)
    (W := modelOf (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)))
    ((boundedFlatCoefficientSupportedFiberAcyclicEquivalence f T a).trans AsSmall.equiv)
    ((boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a).comp
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).smallModel_up_exact)
    ((acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).smallModel_down_exact.comp
      (boundedFlatCoefficientSupportedAcyclicToFiber_exact f T a))
    (auxiliaryNativeFiberAcyclicModelMap f T a).zero

/-- Actual native conversion retains the original exact K-map and stable representative. -/
theorem auxiliaryNativeFiberAcyclicModelMap_stable (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map
        (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a))
        (modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n (Additive.ofMul x)) =
      originalKStableEquiv (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)) n
        (Additive.ofMul
          (KMap (boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a) n x)) := by
  let N := boundedFlatCoefficientSupportedOpenNested f T a
  let A : Model.{u + 1} := ⟨Cat.of (AcyclicCategory N), acyclicStructure N⟩
  let g : boundedFlatCoefficientSupportedFiberModel f T a ⟶ A :=
    ⟨boundedFlatCoefficientSupportedFiberToAcyclic f T a,
      boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a, rfl⟩
  let j : A ⟶ modelOf A.waldhausen :=
    ⟨AsSmall.up, A.waldhausen.smallModel_up_exact, rfl⟩
  have hj : g ≫ j = auxiliaryNativeFiberAcyclicModelMap f T a := by
    apply Model.Hom.ext
    rfl
  have hm := congrArg prespectrumFunctor.map hj
  rw [Functor.map_comp] at hm
  have hn := modelKStableEquiv_naturality g n x
  have hu := boundedFlatCoefficientNativeSmallModelMap_stable A j rfl n (KMap g.exact n x)
  have hp := ConcreteCategory.congr_hom
    (congrArg (stableHomotopyFunctor (n : ℤ)).map hm)
    (modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n (Additive.ofMul x))
  have hc := ConcreteCategory.congr_hom
    ((stableHomotopyFunctor (n : ℤ)).map_comp (prespectrumMap g) (prespectrumMap j))
    (modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n (Additive.ofMul x))
  exact hp.symm.trans (hc.trans ((congrArg
    ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap j)) hn.symm).trans hu))

end Quillen.PerfectComplexes
