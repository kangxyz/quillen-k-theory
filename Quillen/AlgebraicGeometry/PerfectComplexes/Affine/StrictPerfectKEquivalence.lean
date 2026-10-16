/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.OppositeJointData
public import Quillen.Waldhausen.WeakArrow.JointData
public import Quillen.Waldhausen.Approximation.Dual
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.WeakArrowFactorization
public import Quillen.AlgebraicGeometry.PerfectComplexes.GilletWaldhausen
public import Quillen.Waldhausen.WeakArrow.KEquivalence

/-!
# Original affine strict-perfect and locally-perfect K equivalences

For every commutative ring and every connective degree, including K₀, the
original `strictToPerfectKMap` and the original public
`vectorBundleToPerfectKMap` are bijective. The corresponding multiplicative
equivalences retain those exact forward maps, and their original
vector-bundle comparison triangle commutes.

The proof follows the weak-arrow and dual-approximation method of
Thomason–Trobaugh, Theorem 1.9.8. Actual affine derived roofs give literal
incoming factorization through degreewise split epimorphisms with original
perfect kernels. Constructed coherent opposite cocylinders give genuine
joint data. Actual dual S-construction reversal and the original weak-arrow
first-leg comparison complete the original K-map proof. No approximation,
cylinder, strictification, or K-equivalence hypothesis remains.

Targets are the original locally-perfect complexes of arbitrary module
sheaves. No termwise quasi-coherence, regularity, noetherianity, or
nontrivial-ring hypothesis is imposed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

/-- Exactness of the unchanged original strict-to-perfect inclusion. -/
abbrev strictToPerfectExact (X : Scheme.{u}) :
    IsExact (strictWaldhausen X).cof (strictWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (strictToPerfect X) :=
  subcategoryInclusion_exact (strictPerfect X) (locallyPerfect X)
    (fun _ h => locallyPerfect_of_strictPerfect h)

/-- The literal opposite weak-arrow category for the original inclusion. -/
abbrev strictToPerfectWeakArrowOpposite (X : Scheme.{u}) :=
  WeakArrow.dualWaldhausenStructure (strictWaldhausen X) (perfectWaldhausen X)
    (strictOppositeWaldhausen X) (perfectOppositeWaldhausen X) (strictToPerfect X)
    (strictToPerfectExact X) (strictToPerfect_op_exact X) (perfectOppositeWaldhausen_compatible X)

/-- Constructed coherent joint data on the literal opposite weak-arrow
category for the original inclusion, on every scheme. -/
def strictToPerfectWeakArrowJointData (X : Scheme.{u}) :
    Fibration.RowFactorization.JointData
      (Fibration.NestedWeakEquivalences.refl (strictToPerfectWeakArrowOpposite X)) :=
  WeakArrow.dualJointData (strictWaldhausen X) (perfectWaldhausen X)
    (strictOppositeWaldhausen X) (perfectOppositeWaldhausen X) (strictToPerfect X)
    (strictToPerfectExact X) (strictToPerfect_op_exact X) (perfectOppositeWaldhausen_compatible X)
    (strictOppositeJointData X) (perfectOppositeJointData X) (strictToPerfectOpJointIso X)
    (strictToPerfectOpJointIso_inv_inl X) (strictToPerfectOpJointIso_inv_inr X)
    (strictToPerfectOpJointIso_inv_projection X)

/-- The literal affine target projection satisfies actual dual approximation.
Its incoming factorization uses original chain maps and actual kernel sequences. -/
lemma strictToPerfect_target_hasDualApproximation (R : CommRingCat.{u}) :
    HasDualApproximationProperty
      (WeakArrow.waldhausenStructure (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
        (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)))
      (perfectWaldhausen (Spec R)) (strictToPerfectWeakArrowOpposite (Spec R)).cof.unop
      (WeakArrow.target (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R))) := by
  let : (perfectWaldhausen (Spec R)).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (locallyPerfect (Spec R))
  constructor
  · intro X Y f hf
    exact WeakArrow.target_reflects (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)) (fun _ h => h) f hf
  · intro X B' b
    obtain ⟨Y, f, v, hv, he, hc, hd, hkc, hkd⟩ := weakArrow_target_dual_factorization R X B' b
    refine ⟨Y, f, v, ?_, hv, he⟩
    have : Epi f.hom.left.hom := HomologicalComplex.epi_of_epi_f _
      (fun i => by have := hc i; infer_instance)
    have : Epi f.hom.right.hom := HomologicalComplex.epi_of_epi_f _
      (fun i => by have := hd i; infer_instance)
    constructor
    · apply (ExactSubcategory.deflation_iff (abelianExactStructure
        (CochainComplex (Spec R).Modules ℤ))
        (strictPerfect (Spec R)) f.hom.left).mpr
      refine ⟨kernel f.hom.left.hom, hkc, kernel.ι f.hom.left.hom,
        kernel.condition f.hom.left.hom, ?_⟩
      exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f.hom.left.hom)
              mono_f := inferInstance
              epi_g := inferInstance }
    · apply (ExactSubcategory.deflation_iff (abelianExactStructure
        (CochainComplex (Spec R).Modules ℤ))
        (locallyPerfect (Spec R)) f.hom.right).mpr
      refine ⟨kernel f.hom.right.hom, hkd, kernel.ι f.hom.right.hom,
        kernel.condition f.hom.right.hom, ?_⟩
      exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f.hom.right.hom)
              mono_f := inferInstance
              epi_g := inferInstance }

/-- The original strict-to-perfect K-map is bijective over every commutative
ring and in every connective degree, including zero. All structural inputs
are constructed from genuine geometric and chain-level data. -/
lemma strictToPerfectKMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (strictToPerfectKMap (Spec R) n) := by
  let : (perfectWaldhausen (Spec R)).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (locallyPerfect (Spec R))
  apply (WeakArrow.KMap_bijective_iff_target.{u+1,u} (strictWaldhausen (Spec R))
    (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R))
    (strictToPerfectExact (Spec R)) n).mpr
  exact KMap_bijective_of_dualApproximation
    (WeakArrow.dual_compatible (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictOppositeWaldhausen (Spec R)) (perfectOppositeWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)) (strictToPerfect_op_exact (Spec R))
      (perfectOppositeWaldhausen_compatible (Spec R)) (strictOppositeWaldhausen_compatible (Spec
        R)))
    (perfectOppositeWaldhausen_compatible (Spec R))
    (WeakArrow.target_exact (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)))
    (WeakArrow.dual_target_exact (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictOppositeWaldhausen (Spec R)) (perfectOppositeWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)) (strictToPerfect_op_exact (Spec R))
      (perfectOppositeWaldhausen_compatible (Spec R)))
    (strictToPerfect_target_hasDualApproximation R) (strictToPerfectWeakArrowJointData (Spec R)) n

/-- The original public scheme K to locally-perfect K-map is bijective in
every connective degree over every commutative ring. -/
lemma vectorBundleToPerfectKMap_bijective (R : CommRingCat.{u}) (n : ℕ) :
    Function.Bijective (vectorBundleToPerfectKMap (Spec R) n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap]
  exact (strictToPerfectKMap_bijective R n).comp (vectorBundleToStrictKMap_bijective (Spec R) n)

/-- Affine strict/perfect comparison with exactly the original forward map. -/
def strictToPerfectKEquiv (R : CommRingCat.{u}) (n : ℕ) :
    StrictK (Spec R) n ≃* PerfectK (Spec R) n :=
  MulEquiv.ofBijective (strictToPerfectKMap (Spec R) n) (strictToPerfectKMap_bijective R n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma strictToPerfectKEquiv_coe (R : CommRingCat.{u}) (n : ℕ) :
    ↑(strictToPerfectKEquiv R n) = strictToPerfectKMap (Spec R) n := rfl

/-- Original scheme Q-theory and all-sheaf locally-perfect K-theory agree on
every affine scheme through the unchanged public comparison homomorphism. -/
def vectorBundleToPerfectKEquiv (R : CommRingCat.{u}) (n : ℕ) :
    AlgebraicGeometry.Scheme.K (Spec R) n ≃* PerfectK (Spec R) n :=
  MulEquiv.ofBijective (vectorBundleToPerfectKMap (Spec R) n)
    (vectorBundleToPerfectKMap_bijective R n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma vectorBundleToPerfectKEquiv_coe (R : CommRingCat.{u}) (n : ℕ) :
    ↑(vectorBundleToPerfectKEquiv R n) = vectorBundleToPerfectKMap (Spec R) n := rfl

/-- The affine equivalences retain the actual original vector-bundle triangle. -/
lemma vectorBundleToStrictKEquiv_trans (R : CommRingCat.{u}) (n : ℕ) :
    (vectorBundleToStrictKEquiv (Spec R) n).trans (strictToPerfectKEquiv R n) =
      vectorBundleToPerfectKEquiv R n := by
  ext x
  exact DFunLike.congr_fun (strictToPerfect_comp_vectorBundleToStrictKMap (Spec R) n) x

end Quillen.PerfectComplexes.Affine
