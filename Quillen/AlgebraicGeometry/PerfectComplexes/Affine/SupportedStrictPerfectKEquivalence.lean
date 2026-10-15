/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedWeakArrowFactorization
public import Quillen.Waldhausen.WeakArrow.JointData
public import Quillen.Waldhausen.Approximation.Dual
public import Quillen.Waldhausen.WeakArrow.KEquivalence

/-!
# The original supported affine strict-perfect K-equivalence

For every ring, arbitrary open immersion `j : U ⟶ Spec R`, and connective degree
including zero, the existing `strictSupportedToPerfectKMap` is bijective. The
constructed equivalence has that literal forward map, and forgetting support
commutes with the original absolute comparison maps.

This follows from the genuine supported weak-arrow dual approximation and
constructed coherent cocylinders. It is not inferred from an absolute
K-equivalence. Targets remain arbitrary all-sheaf locally perfect complexes;
no termwise quasicoherence or quasi-compactness of the open is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.Waldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

/-- The dual Waldhausen structure on weak arrows for the inclusion of strict-supported complexes
into perfect-supported complexes along `j`. -/
abbrev supportedStrictToPerfectWeakArrowOpposite {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :=
  WeakArrow.dualWaldhausenStructure (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
    (strictSupportedOppositeWaldhausen j) (perfectSupportedOppositeWaldhausen j)
    (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j)
      (strictSupportedToPerfect_op_exact j)
    (perfectSupportedOppositeWaldhausen_compatible j)

/-- Joint row-factorization data for the dual weak-arrow structure of the strict-supported
inclusion, using the compatible ambient cocylinders. -/
def supportedStrictToPerfectWeakArrowJointData {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (supportedStrictToPerfectWeakArrowOpposite j)) :=
  WeakArrow.dualJointData (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
    (strictSupportedOppositeWaldhausen j) (perfectSupportedOppositeWaldhausen j)
    (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j)
      (strictSupportedToPerfect_op_exact j)
    (perfectSupportedOppositeWaldhausen_compatible j)
    (strictSupportedOppositeJointData j) (perfectSupportedOppositeJointData j)
    (strictSupportedToPerfectOpJointIso j) (strictSupportedToPerfectOpJointIso_inv_inl j)
    (strictSupportedToPerfectOpJointIso_inv_inr j)
      (strictSupportedToPerfectOpJointIso_inv_projection j)

lemma supportedStrictToPerfect_target_hasDualApproximation (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] :
    HasDualApproximationProperty
      (WeakArrow.waldhausenStructure (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
        (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j))
      (perfectSupportedWaldhausen j) (supportedStrictToPerfectWeakArrowOpposite j).cof.unop
      (WeakArrow.target (perfectSupportedWaldhausen j) (strictSupportedToPerfect j)) := by
  let : (perfectSupportedWaldhausen j).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (perfectSupported j)
  constructor
  · intro X Y f hf
    exact WeakArrow.target_reflects (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
      (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j) (fun _ h => h) f hf
  · intro X B' b
    obtain ⟨Y, f, v, hv, he, hc, hd, hkc, hkd⟩ :=
      supported_weakArrow_target_dual_factorization R j X B' b
    refine ⟨Y, f, v, ?_, hv, he⟩
    have : Epi f.hom.left.hom := HomologicalComplex.epi_of_epi_f _
      (fun i => by have := hc i; infer_instance)
    have : Epi f.hom.right.hom := HomologicalComplex.epi_of_epi_f _
      (fun i => by have := hd i; infer_instance)
    constructor
    · apply (CategoryTheory.ExactCategory.ExactSubcategory.deflation_iff
      (Quillen.abelianExactStructure (Complex
        (Spec R)))
        (strictSupported j) f.hom.left).mpr
      refine ⟨kernel f.hom.left.hom, hkc, kernel.ι f.hom.left.hom,
        kernel.condition f.hom.left.hom, ?_⟩
      exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f.hom.left.hom)
              mono_f := inferInstance
              epi_g := inferInstance }
    · apply (CategoryTheory.ExactCategory.ExactSubcategory.deflation_iff
      (Quillen.abelianExactStructure (Complex
        (Spec R)))
        (perfectSupported j) f.hom.right).mpr
      refine ⟨kernel f.hom.right.hom, hkd, kernel.ι f.hom.right.hom,
        kernel.condition f.hom.right.hom, ?_⟩
      exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f.hom.right.hom)
              mono_f := inferInstance
              epi_g := inferInstance }

/-- Genuine supported enhancement for the original supported K-map, proved
from the actual supported weak-arrow approximation rather than from absolute K. -/
lemma strictSupportedToPerfectKMap_bijective (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    Function.Bijective (strictSupportedToPerfectKMap j n) := by
  let : (perfectSupportedWaldhausen j).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (perfectSupported j)
  apply (WeakArrow.KMap_bijective_iff_target.{u+1,u} (strictSupportedWaldhausen j)
    (perfectSupportedWaldhausen j) (strictSupportedToPerfect j)
    (strictSupportedToPerfect_exact j) n).mpr
  exact KMap_bijective_of_dualApproximation
    (WeakArrow.dual_compatible (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
      (strictSupportedOppositeWaldhausen j) (perfectSupportedOppositeWaldhausen j)
      (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j)
      (strictSupportedToPerfect_op_exact j) (perfectSupportedOppositeWaldhausen_compatible j)
      (strictSupportedOppositeWaldhausen_compatible j))
    (perfectSupportedOppositeWaldhausen_compatible j)
    (WeakArrow.target_exact (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
      (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j))
    (WeakArrow.dual_target_exact (strictSupportedWaldhausen j) (perfectSupportedWaldhausen j)
      (strictSupportedOppositeWaldhausen j) (perfectSupportedOppositeWaldhausen j)
      (strictSupportedToPerfect j) (strictSupportedToPerfect_exact j)
      (strictSupportedToPerfect_op_exact j) (perfectSupportedOppositeWaldhausen_compatible j))
    (supportedStrictToPerfect_target_hasDualApproximation R j)
    (supportedStrictToPerfectWeakArrowJointData j) n

/-- Every degree, including zero, retains exactly the original supported forward map. -/
def strictSupportedToPerfectKEquiv (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    StrictSupportedK j n ≃* PerfectSupportedK j n :=
  MulEquiv.ofBijective (strictSupportedToPerfectKMap j n)
    (strictSupportedToPerfectKMap_bijective R j n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma strictSupportedToPerfectKEquiv_coe (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    ↑(strictSupportedToPerfectKEquiv R j n) = strictSupportedToPerfectKMap j n := rfl

/-- Forgetting support commutes with the unchanged original comparison maps. -/
lemma strictSupportedToPerfectKMap_inclusion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (perfectSupportedKMap j n).comp (strictSupportedToPerfectKMap j n) =
      (strictToPerfectKMap X n).comp (strictSupportedKMap j n) := by
  change (KMap (subcategoryInclusion_exact (perfectSupported j) (locallyPerfect X)
    (fun _ h => h.1)) n).comp (KMap (strictSupportedToPerfect_exact j) n) =
      (KMap (subcategoryInclusion_exact (strictPerfect X) (locallyPerfect X)
        (fun _ h => locallyPerfect_of_strictPerfect h)) n).comp
      (KMap (subcategoryInclusion_exact (strictSupported j) (strictPerfect X)
        (fun _ h => h.1)) n)
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes.Affine
