/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBundle
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativePhiComparison

/-! # The original model Phi is bijective on qcqs schemes

The actual comparison square and the two literal perfect inclusions transport
the unchanged native two-summand bijection to the original flasque model.
This argument uses no coefficient inverse law and applies in every natural degree.
-/
@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeGlobal

/-- The equivalence induced by the literal original perfect inclusion. -/
def modelInclusionKEquiv (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen X).K n ≃* PerfectK X n :=
  MulEquiv.ofBijective (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X) n)
    (FlasqueBoundedBelow.perfectInclusion_KMap_bijective X n)

lemma modelInclusionKEquiv_apply (X : Scheme.{u}) [CompactSpace X] (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen X).K n) :
    modelInclusionKEquiv X n a =
      Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X) n a := rfl

/-- The product of the same original inclusions, retaining the ordered factors. -/
def modelProductInclusionKEquiv (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen X.obj).K n ×
        (FlasqueBoundedBelow.waldhausen X.obj).K n ≃*
      PerfectK X.obj n × PerfectK X.obj n :=
  (modelInclusionKEquiv X.obj n).prodCongr (modelInclusionKEquiv X.obj n)

lemma modelProductInclusionKEquiv_apply (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    modelProductInclusionKEquiv X n (a, b) =
      (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n a,
        Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n b) := rfl

/-- The existing native comparison square, expressed using its literal K-equivalences. -/
theorem PhiTwoSummandKMap_native_square (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen X.obj).K n ×
      (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    modelInclusionKEquiv (nativeLineFunctor.obj X).obj n
        (P5NativePhi.PhiTwoSummandKMap X n a) =
      nativeTwoSummandKMap X n (modelProductInclusionKEquiv X n a) :=
  P5NativePhi.PhiTwoSummandKMap_native X n a.1 a.2

/-- Model Phi is bijective from the unchanged native square, including degree zero. -/
theorem PhiTwoSummandKMap_qcqs_bijective (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    Function.Bijective (P5NativePhi.PhiTwoSummandKMap X n) := by
  constructor
  · intro a b hab
    apply (modelProductInclusionKEquiv X n).injective
    apply (nativeTwoSummandKMap_qcqs_bijective X n).1
    rw [← PhiTwoSummandKMap_native_square, ← PhiTwoSummandKMap_native_square, hab]
  · intro y
    obtain ⟨z, hz⟩ := (nativeTwoSummandKMap_qcqs_bijective X n).2
      (modelInclusionKEquiv (nativeLineFunctor.obj X).obj n y)
    refine ⟨(modelProductInclusionKEquiv X n).symm z, ?_⟩
    apply (modelInclusionKEquiv (nativeLineFunctor.obj X).obj n).injective
    rw [PhiTwoSummandKMap_native_square, MulEquiv.apply_symm_apply, hz]

/-- The model equivalence has the literal original Phi map as its forward map. -/
def modelPhiKEquiv (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen X.obj).K n ×
        (FlasqueBoundedBelow.waldhausen X.obj).K n ≃*
      (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n :=
  MulEquiv.ofBijective (P5NativePhi.PhiTwoSummandKMap X n)
    (PhiTwoSummandKMap_qcqs_bijective X n)

lemma modelPhiKEquiv_apply (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj]
    (n : ℕ) (a : (FlasqueBoundedBelow.waldhausen X.obj).K n ×
      (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    modelPhiKEquiv X n a = P5NativePhi.PhiTwoSummandKMap X n a := rfl

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeGlobal
