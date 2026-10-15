/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePhiSecondEntry

/-!
# Actual original GPhi matrix on the original flasque coefficient K-groups

The four strict-source entries and the actual source KMap surjectivity give
both original chosen-zero embedding formulas. The unchanged product KEquiv
and original group law then assemble GPhi, including degree zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
open StrictPositiveRetraction FlasqueTwoSummands FlasqueCoefficients

/-- The actual original first embedding is (a,1) under the unchanged product KEquiv. -/
lemma firstInjection_KEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n
        (Waldhausen.KMap (firstInjection_exact R) n a) = (a, 1) := by
  let W := FlasqueBoundedBelow.waldhausen (Spec R)
  have h := Waldhausen.Product.KEquiv_pair_apply W W W (Waldhausen.IsExact.id W.cof W.weq)
    (Waldhausen.zeroFunctor_isExact W W) n a
  simpa only [Waldhausen.KMap_id, Waldhausen.KMap_zeroFunctor,
    MonoidHom.id_apply, MonoidHom.one_apply] using h

/-- The actual original second embedding is (1,a), retaining its original zero rebasing. -/
lemma secondInjection_KEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n
        (Waldhausen.KMap (secondInjection_exact R) n a) = (1, a) := by
  let W := FlasqueBoundedBelow.waldhausen (Spec R)
  have h := Waldhausen.Product.KEquiv_pair_apply W W W
    (Waldhausen.zeroFunctor_isExact W W) (Waldhausen.IsExact.id W.cof W.weq) n a
  simpa only [Waldhausen.KMap_id, Waldhausen.KMap_zeroFunctor,
    MonoidHom.id_apply, MonoidHom.one_apply] using h

lemma firstInjection_KEquiv_symm (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n).symm (a, 1) =
        Waldhausen.KMap (firstInjection_exact R) n a := by
  apply (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
    (FlasqueBoundedBelow.waldhausen (Spec R)) n).injective
  exact (MulEquiv.apply_symm_apply _ _).trans (firstInjection_KEquiv_apply R n a).symm

lemma secondInjection_KEquiv_symm (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n).symm (1, a) =
        Waldhausen.KMap (secondInjection_exact R) n a := by
  apply (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
    (FlasqueBoundedBelow.waldhausen (Spec R)) n).injective
  exact (MulEquiv.apply_symm_apply _ _).trans (secondInjection_KEquiv_apply R n a).symm

/-- Original paired G maps are exactly its two original coefficient K-maps. -/
lemma G_KEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n) :
    Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n (Waldhausen.KMap (G_exact R) n a) =
        (Waldhausen.KMap (G0_exact R) n a, Waldhausen.KMap (G1_exact R) n a) :=
  Waldhausen.Product.KEquiv_pair_apply (FlasqueBoundedBelow.waldhausen (twoChartLine R))
    (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))
    (G0_exact R) (G1_exact R) n a

/-- The actual GPhi map uses the unchanged product KEquiv on both sides. -/
def GPhiPairKMap (R : CommRingCat.{u}) (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).K n ×
      (FlasqueBoundedBelow.waldhausen (Spec R)).K n →*
        (FlasqueBoundedBelow.waldhausen (Spec R)).K n ×
          (FlasqueBoundedBelow.waldhausen (Spec R)).K n :=
  (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
    (FlasqueBoundedBelow.waldhausen (Spec R)) n).toMonoidHom.comp
      ((Waldhausen.KMap (G_exact R) n).comp (PhiTwoSummandKMap R n))

lemma G0First_originalFormula (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (G0_exact R) n).comp
      (((Waldhausen.KMap (Phi_exact R) n).comp (Waldhausen.KMap (firstInjection_exact R) n)).comp
        (Waldhausen.KMap (strictTotal_exact (Spec R)) n)) =
      Waldhausen.KMap (strictTotal_exact (Spec R)) n := by
  rw [Waldhausen.KMap_comp_KMap (firstInjection_exact R) (Phi_exact R) n,
    Waldhausen.KMap_comp_KMap (strictTotal_exact (Spec R))
      ((firstInjection_exact R).comp (Phi_exact R)) n]
  exact (Waldhausen.KMap_comp_KMap (strictPhiFirst_exact R) (G0_exact R) n).trans
    (G0First_KMap_eq_strictTotal R n)

lemma G1First_originalFormula (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (G1_exact R) n).comp
      (((Waldhausen.KMap (Phi_exact R) n).comp (Waldhausen.KMap (firstInjection_exact R) n)).comp
        (Waldhausen.KMap (strictTotal_exact (Spec R)) n)) = 1 := by
  rw [Waldhausen.KMap_comp_KMap (firstInjection_exact R) (Phi_exact R) n,
    Waldhausen.KMap_comp_KMap (strictTotal_exact (Spec R))
      ((firstInjection_exact R).comp (Phi_exact R)) n]
  exact (Waldhausen.KMap_comp_KMap (strictPhiFirst_exact R) (G1_exact R) n).trans
    (G1First_KMap_eq_one R n)

lemma G0Second_originalFormula (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (G0_exact R) n).comp
      (((Waldhausen.KMap (Phi_exact R) n).comp (Waldhausen.KMap (secondInjection_exact R) n)).comp
        (Waldhausen.KMap (strictTotal_exact (Spec R)) n)) = 1 := by
  rw [Waldhausen.KMap_comp_KMap (secondInjection_exact R) (Phi_exact R) n,
    Waldhausen.KMap_comp_KMap (strictTotal_exact (Spec R))
      ((secondInjection_exact R).comp (Phi_exact R)) n]
  exact (Waldhausen.KMap_comp_KMap (strictPhiSecond_exact R) (G0_exact R) n).trans
    (G0Second_KMap_eq_one R n)

lemma G1Second_originalFormula (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (G1_exact R) n).comp
      (((Waldhausen.KMap (Phi_exact R) n).comp (Waldhausen.KMap (secondInjection_exact R) n)).comp
        (Waldhausen.KMap (strictTotal_exact (Spec R)) n)) =
      Waldhausen.KMap (strictTotal_exact (Spec R)) n := by
  rw [Waldhausen.KMap_comp_KMap (secondInjection_exact R) (Phi_exact R) n,
    Waldhausen.KMap_comp_KMap (strictTotal_exact (Spec R))
      ((secondInjection_exact R).comp (Phi_exact R)) n]
  exact (Waldhausen.KMap_comp_KMap (strictPhiSecond_exact R) (G1_exact R) n).trans
    (G1Second_KMap_eq_strictTotal R n)

/-- Both actual GPhi entries on the first original source embedding. -/
lemma GPhiPairKMap_source_one_right (R : CommRingCat.{u}) (n : ℕ)
    (a : (strictWaldhausen (Spec R)).K n) :
    GPhiPairKMap R n (Waldhausen.KMap (strictTotal_exact (Spec R)) n a, 1) =
      (Waldhausen.KMap (strictTotal_exact (Spec R)) n a, 1) := by
  change Waldhausen.Product.KEquiv _ _ n (Waldhausen.KMap (G_exact R) n
    (Waldhausen.KMap (Phi_exact R) n ((Waldhausen.Product.KEquiv _ _ n).symm _))) = _
  rw [firstInjection_KEquiv_symm, G_KEquiv_apply]
  exact _root_.Prod.ext (DFunLike.congr_fun (G0First_originalFormula R n) a)
    (DFunLike.congr_fun (G1First_originalFormula R n) a)

/-- Both actual GPhi entries on the second original source embedding. -/
lemma GPhiPairKMap_source_one_left (R : CommRingCat.{u}) (n : ℕ)
    (a : (strictWaldhausen (Spec R)).K n) :
    GPhiPairKMap R n (1, Waldhausen.KMap (strictTotal_exact (Spec R)) n a) =
      (1, Waldhausen.KMap (strictTotal_exact (Spec R)) n a) := by
  change Waldhausen.Product.KEquiv _ _ n (Waldhausen.KMap (G_exact R) n
    (Waldhausen.KMap (Phi_exact R) n ((Waldhausen.Product.KEquiv _ _ n).symm _))) = _
  rw [secondInjection_KEquiv_symm, G_KEquiv_apply]
  exact _root_.Prod.ext (DFunLike.congr_fun (G0Second_originalFormula R n) a)
    (DFunLike.congr_fun (G1Second_originalFormula R n) a)

/-- Actual source surjectivity transports the first column to every original flasque K input. -/
lemma GPhiPairKMap_one_right (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    GPhiPairKMap R n (a, 1) = (a, 1) := by
  obtain ⟨x, rfl⟩ := (strictTotal_KMap_bijective R n).2 a
  exact GPhiPairKMap_source_one_right R n x

/-- Actual source surjectivity transports the second column to all original flasque K inputs. -/
lemma GPhiPairKMap_one_left (R : CommRingCat.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    GPhiPairKMap R n (1, a) = (1, a) := by
  obtain ⟨x, rfl⟩ := (strictTotal_KMap_bijective R n).2 a
  exact GPhiPairKMap_source_one_left R n x

/-- The original product group decomposition assembles the actual GPhi matrix, including n=0. -/
theorem GPhiPairKMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    GPhiPairKMap R n (a, b) = (a, b) := by
  calc
    _ = GPhiPairKMap R n ((a, 1) * (1, b)) := by simp
    _ = GPhiPairKMap R n (a, 1) * GPhiPairKMap R n (1, b) := map_mul _ _ _
    _ = (a, 1) * (1, b) := by rw [GPhiPairKMap_one_right, GPhiPairKMap_one_left]
    _ = _ := by simp

/-- Original chosen-zero KMaps give G after Phi equal to the identity, without a PhiG claim. -/
theorem G_comp_Phi_KMap (R : CommRingCat.{u}) (n : ℕ) :
    (Waldhausen.KMap (G_exact R) n).comp (Waldhausen.KMap (Phi_exact R) n) =
      MonoidHom.id ((Waldhausen.ExtensionCategory.productStructure
        (FlasqueBoundedBelow.waldhausen (Spec R))
        (FlasqueBoundedBelow.waldhausen (Spec R))).K n) := by
  apply MonoidHom.ext
  intro x
  apply (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
    (FlasqueBoundedBelow.waldhausen (Spec R)) n).injective
  have h := GPhiPairKMap_apply R n
    ((Waldhausen.Product.KEquiv _ _ n) x).1 ((Waldhausen.Product.KEquiv _ _ n) x).2
  change Waldhausen.Product.KEquiv _ _ n (Waldhausen.KMap (G_exact R) n
    (Waldhausen.KMap (Phi_exact R) n ((Waldhausen.Product.KEquiv _ _ n).symm
      ((Waldhausen.Product.KEquiv _ _ n) x)))) = _ at h
  simpa only [MulEquiv.symm_apply_apply, MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The same identity is the original canonical KMap of the actual functor composite. -/
theorem GPhi_KMap_id (R : CommRingCat.{u}) (n : ℕ) :
    Waldhausen.KMap ((Phi_exact R).comp (G_exact R)) n =
      MonoidHom.id ((Waldhausen.ExtensionCategory.productStructure
        (FlasqueBoundedBelow.waldhausen (Spec R)) (FlasqueBoundedBelow.waldhausen (Spec R))).K n) :=
  (Waldhausen.KMap_comp_KMap (Phi_exact R) (G_exact R) n).symm.trans (G_comp_Phi_KMap R n)

end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
