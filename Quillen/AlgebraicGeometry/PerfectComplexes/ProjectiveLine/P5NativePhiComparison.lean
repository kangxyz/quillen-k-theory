/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhi
public import Quillen.Waldhausen.Product.Functoriality

/-! # Literal native forward K-map correspondence for the original flasque Phi

The same actual total augmentation and categorical coproduct comparison retain
the existing native perfect two-summand functor and original product K-equivalence.
No affine transport, derived-category replacement or K-equivalence premise is used.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
open FlasqueTwoSummands

/-- The literal product of the existing original model inclusions. -/
def inputInclusion (X : QuasiCompactSchemes.{u}) :
    FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj ⥤
      Perfect X.obj × Perfect X.obj :=
  (FlasqueBoundedBelow.perfectInclusion X.obj).prod
    (FlasqueBoundedBelow.perfectInclusion X.obj)

lemma inputInclusion_exact (X : QuasiCompactSchemes.{u}) : Waldhausen.IsExact
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).cof
    (Waldhausen.ExtensionCategory.productStructure
      (FlasqueBoundedBelow.waldhausen X.obj) (FlasqueBoundedBelow.waldhausen X.obj)).weq
    (Waldhausen.ExtensionCategory.productStructure
      (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)).cof
    (Waldhausen.ExtensionCategory.productStructure
      (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)).weq (inputInclusion X) :=
  Waldhausen.ExtensionCategory.pair_exact _ _ _
    ((Waldhausen.ExtensionCategory.fst_exact _ _).comp
      (FlasqueBoundedBelow.perfectInclusion_exact X.obj))
    ((Waldhausen.ExtensionCategory.snd_exact _ _).comp
      (FlasqueBoundedBelow.perfectInclusion_exact X.obj))
/-- Actual pre-total sum after the literal inclusion is the local original sum. -/
def beforeTotalInclusionIso (X : QuasiCompactSchemes.{u}) :
    beforeTotal X ⋙ BoundedBelow.inclusion (nativeLineFunctor.obj X).obj ≅
      inputInclusion X ⋙ nativeTwoSummands X :=
  (boundedSumInclusionIso (nativeLineFunctor.obj X).obj
    (CategoryTheory.Prod.fst _ _ ⋙ first X) (CategoryTheory.Prod.snd _ _ ⋙ second X)).symm

/-- The actual total augmentation transported by the literal original perfect inclusion. -/
def PhiPerfectUnit (X : QuasiCompactSchemes.{u}) :
    beforeTotal X ⋙ BoundedBelow.inclusion (nativeLineFunctor.obj X).obj ⟶
      Phi X ⋙ FlasqueBoundedBelow.perfectInclusion (nativeLineFunctor.obj X).obj :=
  CategoryTheory.Functor.whiskerRight (PhiUnit X) (BoundedBelow.inclusion (nativeLineFunctor.obj
    X).obj)

lemma PhiPerfectUnit_weak (X : QuasiCompactSchemes.{u})
    (K : FlasqueBoundedBelow.Obj X.obj × FlasqueBoundedBelow.Obj X.obj) :
    (perfectWaldhausen (nativeLineFunctor.obj X).obj).weq ((PhiPerfectUnit X).app K) :=
  (BoundedBelow.inclusion_exact _).weak _ (PhiUnit_weak X K)

/-- The induced local original K-map is recovered by exact functors and an actual weak unit. -/
lemma Phi_KMap_after_perfectInclusion (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (nativeLineFunctor.obj X).obj)
      n).comp
        (Waldhausen.KMap (Phi_exact X) n) =
      (Waldhausen.KMap (nativeTwoSummands_exact X) n).comp
        (Waldhausen.KMap (inputInclusion_exact X) n) := by
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  have hw := Waldhausen.KMap_eq_of_weakNatTrans
    ((beforeTotal_exact X).comp (BoundedBelow.inclusion_exact (nativeLineFunctor.obj X).obj))
    ((Phi_exact X).comp (FlasqueBoundedBelow.perfectInclusion_exact (nativeLineFunctor.obj X).obj))
    (PhiPerfectUnit X) (PhiPerfectUnit_weak X) n
  have hi := Waldhausen.KMap_eq_of_iso
    ((beforeTotal_exact X).comp (BoundedBelow.inclusion_exact (nativeLineFunctor.obj X).obj))
    ((inputInclusion_exact X).comp (nativeTwoSummands_exact X)) (beforeTotalInclusionIso X) n
  exact hw.symm.trans hi

/-- The original induced Phi map after the unchanged original product K-equivalence. -/
def PhiTwoSummandKMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen X.obj).K n ×
        (FlasqueBoundedBelow.waldhausen X.obj).K n →*
      (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n :=
  (Waldhausen.KMap (Phi_exact X) n).comp
    (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj)
      (FlasqueBoundedBelow.waldhausen X.obj) n).symm.toMonoidHom

/-- Product inclusion retains both original factor K-maps and the original K-equivalence. -/
lemma inputInclusion_KMap_product (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    Waldhausen.Product.KEquiv (perfectWaldhausen X.obj) (perfectWaldhausen X.obj) n
        (Waldhausen.KMap (inputInclusion_exact X) n
          ((Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj)
            (FlasqueBoundedBelow.waldhausen X.obj) n).symm (a, b))) =
      (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n a,
        Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n b) := by
  let W := FlasqueBoundedBelow.waldhausen X.obj
  let z := (Waldhausen.Product.KEquiv W W n).symm (a, b)
  have hz : (Waldhausen.KMap (Waldhausen.ExtensionCategory.fst_exact W W) n z,
      Waldhausen.KMap (Waldhausen.ExtensionCategory.snd_exact W W) n z) = (a, b) :=
    (Waldhausen.Product.KEquiv W W n).apply_symm_apply _
  have hp := Waldhausen.Product.KEquiv_pair_apply
    (Waldhausen.ExtensionCategory.productStructure W W)
    (perfectWaldhausen X.obj) (perfectWaldhausen X.obj)
    ((Waldhausen.ExtensionCategory.fst_exact W W).comp
      (FlasqueBoundedBelow.perfectInclusion_exact X.obj))
    ((Waldhausen.ExtensionCategory.snd_exact W W).comp
      (FlasqueBoundedBelow.perfectInclusion_exact X.obj)) n z
  rw [← Waldhausen.KMap_comp_KMap (Waldhausen.ExtensionCategory.fst_exact W W)
    (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n,
    ← Waldhausen.KMap_comp_KMap (Waldhausen.ExtensionCategory.snd_exact W W)
      (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n] at hp
  exact hp.trans (congrArg₂
    (fun x y => (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n x,
      Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n y))
    (congrArg _root_.Prod.fst hz) (congrArg _root_.Prod.snd hz))

/-- The existing original nativeTwoSummandKMap is recovered, for every n including zero,
by literal model inclusions on the same original native scheme. -/
theorem PhiTwoSummandKMap_native (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact (nativeLineFunctor.obj X).obj) n
        (PhiTwoSummandKMap X n (a, b)) =
      nativeTwoSummandKMap X n
        (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n a,
          Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n b) := by
  let W := FlasqueBoundedBelow.waldhausen X.obj
  let z := (Waldhausen.Product.KEquiv W W n).symm (a, b)
  have h := DFunLike.congr_fun (Phi_KMap_after_perfectInclusion X n) z
  change _ = Waldhausen.KMap (nativeTwoSummands_exact X) n
    (Waldhausen.KMap (inputInclusion_exact X) n z) at h
  have hp := inputInclusion_KMap_product X n a b
  have hz := congrArg
    (fun x => (Waldhausen.Product.KEquiv (perfectWaldhausen X.obj)
      (perfectWaldhausen X.obj) n).symm x) hp
  rw [MulEquiv.symm_apply_apply] at hz
  exact h.trans (congrArg (Waldhausen.KMap (nativeTwoSummands_exact X) n) hz)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePhi
