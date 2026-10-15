/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeAffineTwoSummands
public import Quillen.Waldhausen.Product.Functoriality

/-!
# Exact original native K-map correspondence for the flasque Phi

Every map here is the original canonical chosen-zero K-map of an actual exact
functor. The actual affine inverse pullback recovers the existing native target,
including its unchanged product K-equivalence in every natural degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-- The original native geometry pullbacks are inverse K-maps by actual composition and identity. -/
lemma nativeTransport_KMap_inverse (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).inv n).comp
        (Waldhausen.KMap (nativeTransport_exact R) n) =
      MonoidHom.id (PerfectK (nativeLineFunctor.obj (affineBase R)).obj n) := by
  change (perfectKFlatPullback (nativeAffineIso R).inv n).comp
    (perfectKFlatPullback (nativeAffineIso R).hom n) = _
  rw [← perfectKFlatPullback_comp]
  simpa only [Iso.inv_hom_id] using
    (perfectKFlatPullback_id (nativeLineFunctor.obj (affineBase R)).obj n)

/-- Original Phi after literal model inclusion and actual affine inverse transport is
exactly the EXISTING native two-summand original K-map on the product category. -/
lemma Phi_KMap_native (R : CommRingCat.{u}) (n : ℕ) :
    (perfectKFlatPullback (nativeAffineIso R).inv n).comp
        ((Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (twoChartLine R)) n).comp
          (Waldhausen.KMap (Phi_exact R) n)) =
      (Waldhausen.KMap (nativeTwoSummands_exact (affineBase R)) n).comp
        (Waldhausen.KMap (inputInclusion_exact R) n) := by
  rw [Phi_KMap_after_perfectInclusion, localTwoSummands_KMap_native]
  rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, nativeTransport_KMap_inverse]
  rfl

/-- The original induced Phi map after the unchanged original product K-equivalence. -/
def PhiTwoSummandKMap (R : CommRingCat.{u}) (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen (Spec R)).K n ×
        (FlasqueBoundedBelow.waldhausen (Spec R)).K n →*
      (FlasqueBoundedBelow.waldhausen (twoChartLine R)).K n :=
  (Waldhausen.KMap (Phi_exact R) n).comp
    (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
      (FlasqueBoundedBelow.waldhausen (Spec R)) n).symm.toMonoidHom

/-- Product inclusion retains both original factor K-maps and the original K-equivalence. -/
lemma inputInclusion_KMap_product (R : CommRingCat.{u}) (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    Waldhausen.Product.KEquiv (perfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R)) n
        (Waldhausen.KMap (inputInclusion_exact R) n
          ((Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen (Spec R))
            (FlasqueBoundedBelow.waldhausen (Spec R)) n).symm (a, b))) =
      (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n a,
        Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n b) := by
  let W := FlasqueBoundedBelow.waldhausen (Spec R)
  let z := (Waldhausen.Product.KEquiv W W n).symm (a, b)
  have hz : (Waldhausen.KMap (Waldhausen.ExtensionCategory.fst_exact W W) n z,
      Waldhausen.KMap (Waldhausen.ExtensionCategory.snd_exact W W) n z) = (a, b) :=
    (Waldhausen.Product.KEquiv W W n).apply_symm_apply _
  have hp := Waldhausen.Product.KEquiv_pair_apply
    (Waldhausen.ExtensionCategory.productStructure W W)
    (perfectWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
    ((Waldhausen.ExtensionCategory.fst_exact W W).comp
      (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)))
    ((Waldhausen.ExtensionCategory.snd_exact W W).comp
      (FlasqueBoundedBelow.perfectInclusion_exact (Spec R))) n z
  rw [← Waldhausen.KMap_comp_KMap (Waldhausen.ExtensionCategory.fst_exact W W)
    (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n,
    ← Waldhausen.KMap_comp_KMap (Waldhausen.ExtensionCategory.snd_exact W W)
      (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n] at hp
  exact hp.trans (congrArg₂
    (fun x y => (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n x,
      Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n y))
    (congrArg _root_.Prod.fst hz) (congrArg _root_.Prod.snd hz))

/-- The existing original nativeTwoSummandKMap is recovered, for every n including zero,
by literal model inclusions and the actual affine scheme inverse. -/
theorem PhiTwoSummandKMap_native (R : CommRingCat.{u}) (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen (Spec R)).K n) :
    perfectKFlatPullback (nativeAffineIso R).inv n
        (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (twoChartLine R)) n
          (PhiTwoSummandKMap R n (a, b))) =
      nativeTwoSummandKMap (affineBase R) n
        (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n a,
          Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (Spec R)) n b) := by
  let W := FlasqueBoundedBelow.waldhausen (Spec R)
  let z := (Waldhausen.Product.KEquiv W W n).symm (a, b)
  have h := DFunLike.congr_fun (Phi_KMap_native R n) z
  change _ = Waldhausen.KMap (nativeTwoSummands_exact (affineBase R)) n
    (Waldhausen.KMap (inputInclusion_exact R) n z) at h
  have hp := inputInclusion_KMap_product R n a b
  have hz := congrArg
    (fun x => (Waldhausen.Product.KEquiv (perfectWaldhausen (Spec R))
      (perfectWaldhausen (Spec R)) n).symm x) hp
  rw [MulEquiv.symm_apply_apply] at hz
  exact h.trans (congrArg (Waldhausen.KMap (nativeTwoSummands_exact (affineBase R)) n) hz)

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
