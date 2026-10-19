/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNativeFibration
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryAcyclicEvaluation
public import Quillen.Waldhausen.SmallModel.Connecting

/-!
# Ordinary connecting evaluation for auxiliary-supported coefficient sections

The actual supported evaluation is exact for both original weak structures.
Its common-universe lift therefore preserves the original connecting maps.
The genuine small-model fiber homeomorphism lowers this equation to the
original geometric category, retaining the complete canonical fiber path.
No equality between independently chosen native and geometric zeros is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology
universe u
namespace Quillen.PerfectComplexes
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Genuine exact evaluation carries the original native boundary to the geometric
acyclic boundary in the actual small-model coordinates. -/
theorem boundedFlatCoefficientSupportedAcyclicConnecting_smallModel (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K (n + 1)) :
    KMap ((boundedFlatCoefficientSupportedAcyclicEvaluation_exact f T a).comp
      (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))).smallModel_up_exact) n
      (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
        (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          f T a) n x) =
    (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))).smallModelKEquiv n
      (changeWeakConnectingHom (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a))
        (boundedFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)) n
        (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x)) := by
  exact changeWeakConnectingHom_evaluation
    (boundedFlatCoefficientSupportedOpenNested f T a)
    (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a))
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedOpenEquivalence_functor_exact f T a)
    (boundedFlatCoefficientSupportedAcyclicEvaluation_exact f T a)
    (by
      rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedFlatCoefficientSupportedAcyclicEvaluation_inclusion f T a)
    (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence f T a)
    (boundedFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
      (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)) n x

/-- The original support K-equivalence is computed by actual acyclic evaluation
and geometric flattening, without an independently chosen comparison map. -/
theorem boundedFlatCoefficientSupportedAcyclicSupportKEquiv_evaluation
    (a : Under R) (n : ℕ)
    (x : (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).K n) :
    (boundedFlatPerfectSupportedWaldhausen
      (boundedFlatCoefficientFiberSupportOpen f T a).ι).smallModelKEquiv n
      (boundedFlatCoefficientSupportedAcyclicSupportKEquiv f T a n x) =
    KMap (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)).smallModel n
      (KMap ((boundedFlatCoefficientSupportedAcyclicEvaluation_exact f T a).comp
        (acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a))).smallModel_up_exact) n x) := by
  let B := boundedFlatPerfectSupportedWaldhausen
    (boundedFlatCoefficientFiberSupportOpen f T a).ι
  let A := acyclicStructure (boundedFlatPerfectSupportedOpenNested (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a))
  let hi := boundedFlatCoefficientSupportedAcyclicToFiber_exact f T a
  let he := (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
    (boundedFlatCoefficientFiberSupportOpen f T a).ι).comp B.smallModel_up_exact
  let ha := (boundedFlatCoefficientSupportedAcyclicEvaluation_exact f T a).comp
    A.smallModel_up_exact
  let hg := boundedFlatPerfectSupportedOpenAcyclicToSupported_exact (schemeMap f a)
    (boundedFlatCoefficientSupportOpen Q T a)
  change B.smallModelKEquiv n
    ((B.smallModelKEquiv n).symm (KMap he n (KMap hi n x))) = _
  rw [MulEquiv.apply_symm_apply]
  have hs : boundedFlatCoefficientSupportedAcyclicToFiber f T a ⋙
      (boundedFlatCoefficientSupportedSectionEquivalence
        (boundedFlatCoefficientFiberSupportOpen f T a).ι).functor ⋙ AsSmall.up =
      (boundedFlatCoefficientSupportedAcyclicEvaluation f T a ⋙ AsSmall.up) ⋙
        smallModelFunctor (boundedFlatPerfectSupportedOpenAcyclicToSupported (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a)) := by
    rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]
    exact congrArg (fun F ↦ F ⋙ AsSmall.up)
      (boundedFlatCoefficientSupportedAcyclicToFiber_evaluation f T a)
  have hk := KMap_eq_of_iso (hi.comp he) (ha.comp hg.smallModel) (eqToIso hs) n
  exact (DFunLike.congr_fun (KMap_comp_KMap hi he n) x).trans
    ((DFunLike.congr_fun hk x).trans (DFunLike.congr_fun
      (KMap_comp_KMap ha hg.smallModel n).symm x))

/-- The actual native auxiliary-supported boundary evaluates to the original geometric
bounded-flat supported-open connecting homomorphism in every ordinary K-degree. -/
theorem boundedFlatCoefficientSupportedConnecting_evaluation (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K (n + 1)) :
    boundedFlatCoefficientSupportedAcyclicSupportKEquiv f T a n
      (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
        (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          f T a) n x) =
      boundedFlatPerfectSupportedOpenConnectingHom (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x) := by
  apply ((boundedFlatPerfectSupportedWaldhausen
    (boundedFlatCoefficientFiberSupportOpen f T a).ι).smallModelKEquiv n).injective
  rw [boundedFlatCoefficientSupportedAcyclicSupportKEquiv_evaluation,
    boundedFlatCoefficientSupportedAcyclicConnecting_smallModel]
  exact (DFunLike.congr_fun (smallModelKEquiv_naturality
    (boundedFlatPerfectSupportedOpenAcyclicToSupported_exact (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)) n) _).symm

/-- The original native fiber-to-acyclic equivalence with both original exact functors. -/
def boundedFlatCoefficientSupportedFiberAcyclicKEquiv (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n ≃*
      (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)).K n :=
  KEquivOfExactEquivalence _ _ (boundedFlatCoefficientSupportedFiberAcyclicEquivalence f T a)
    (boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a)
    (boundedFlatCoefficientSupportedAcyclicToFiber_exact f T a) n

/-- Inverting actual native acyclic conversion gives precisely inverse original supported
section evaluation of the original geometric supported-open boundary. -/
theorem boundedFlatCoefficientSupportedFiberAcyclicKEquiv_symm_connecting
    (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K (n + 1)) :
    (boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n).symm
      (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
        (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          f T a) n x) =
      (boundedFlatCoefficientSupportedSectionKEquiv
        (boundedFlatCoefficientFiberSupportOpen f T a).ι n).symm
        (boundedFlatPerfectSupportedOpenConnectingHom (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a) n
          (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x)) := by
  apply (boundedFlatCoefficientSupportedSectionKEquiv
    (boundedFlatCoefficientFiberSupportOpen f T a).ι n).injective
  rw [MulEquiv.apply_symm_apply]
  exact boundedFlatCoefficientSupportedConnecting_evaluation f T a n x

end Quillen.PerfectComplexes
