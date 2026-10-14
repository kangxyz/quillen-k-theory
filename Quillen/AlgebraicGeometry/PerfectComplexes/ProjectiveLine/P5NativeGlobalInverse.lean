/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeGlobalPhi
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeGPhiLaw

/-! # The actual original qcqs projective-line inverse

The actual pair `G = (G0, G1)` retains `G0 = p_*` and the prescribed
`G1 = p_* T(- ⊗ L)[1]`, with right tensor in the original flasque model.
The proved original `GΦ = id` and model Phi bijectivity give `ΦG = id`.
Transport through the literal original model inclusions identifies this same
geometric pair with the existing native two-summand inverse in every natural degree.
-/
@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open Quillen.Scheme Quillen.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeGlobal

/-- The original exact geometric G map, in the ordered original product coordinates. -/
def GPairKMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n →*
      (FlasqueBoundedBelow.waldhausen X.obj).K n ×
        (FlasqueBoundedBelow.waldhausen X.obj).K n :=
  (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj)
    (FlasqueBoundedBelow.waldhausen X.obj) n).toMonoidHom.comp
      (Waldhausen.KMap (P5NativeCoefficients.G_exact X) n)

/-- The two coordinates are exactly the prescribed original G0 and right-tensor G1. -/
lemma GPairKMap_apply (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n) :
    GPairKMap X n a =
      (Waldhausen.KMap (P5NativeCoefficients.G0_exact X) n a,
        Waldhausen.KMap (P5NativeCoefficients.G1_exact X) n a) :=
  P5NativeEntries.G_KEquiv_apply X n a

/-- The actual geometric pair transported by the literal original model inclusions. -/
def nativeGeometricG (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    PerfectK (nativeLineFunctor.obj X).obj n →* PerfectK X.obj n × PerfectK X.obj n :=
  (modelProductInclusionKEquiv X n).toMonoidHom.comp
    ((GPairKMap X n).comp
      (modelInclusionKEquiv (nativeLineFunctor.obj X).obj n).symm.toMonoidHom)

/-- Native G preserves the ordered G0/G1 coordinates of the original geometric map. -/
theorem nativeGeometricG_apply (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : PerfectK (nativeLineFunctor.obj X).obj n) :
    nativeGeometricG X n a =
      (Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n
          (Waldhausen.KMap (P5NativeCoefficients.G0_exact X) n
            ((modelInclusionKEquiv (nativeLineFunctor.obj X).obj n).symm a)),
        Waldhausen.KMap (FlasqueBoundedBelow.perfectInclusion_exact X.obj) n
          (Waldhausen.KMap (P5NativeCoefficients.G1_exact X) n
            ((modelInclusionKEquiv (nativeLineFunctor.obj X).obj n).symm a))) := by
  change modelProductInclusionKEquiv X n (GPairKMap X n _) = _
  rw [GPairKMap_apply, modelProductInclusionKEquiv_apply]
  rfl

/-- The definition transports the literal model G map along the actual inclusion. -/
lemma nativeGeometricG_model_apply (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n) :
    nativeGeometricG X n (modelInclusionKEquiv (nativeLineFunctor.obj X).obj n a) =
      modelProductInclusionKEquiv X n (GPairKMap X n a) := by
  change modelProductInclusionKEquiv X n
    (GPairKMap X n ((modelInclusionKEquiv (nativeLineFunctor.obj X).obj n).symm
      (modelInclusionKEquiv (nativeLineFunctor.obj X).obj n a))) = _
  rw [MulEquiv.symm_apply_apply]

/-- The proved original G-Phi law retains the ordered model K-coordinates. -/
theorem GPairKMap_PhiTwoSummandKMap (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen X.obj).K n ×
      (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    GPairKMap X n (P5NativePhi.PhiTwoSummandKMap X n a) = a :=
  DFunLike.congr_fun (P5NativeEntries.GPhiPairKMap_eq_id X n) a

/-- Surjectivity of the actual original Phi gives the other original inverse law. -/
theorem PhiTwoSummandKMap_GPairKMap (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n) :
    P5NativePhi.PhiTwoSummandKMap X n (GPairKMap X n a) = a := by
  obtain ⟨b, rfl⟩ := (PhiTwoSummandKMap_qcqs_bijective X n).2 a
  rw [GPairKMap_PhiTwoSummandKMap]

/-- The original geometric G is the inverse of the actual model Phi equivalence. -/
theorem modelPhiKEquiv_symm_apply (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ)
    (a : (FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n) :
    (modelPhiKEquiv X n).symm a = GPairKMap X n a := by
  apply (modelPhiKEquiv X n).injective
  exact ((modelPhiKEquiv X n).apply_symm_apply a).trans
    (PhiTwoSummandKMap_GPairKMap X n a).symm

/-- Actual original Phi after actual original G is the identity on the model K group. -/
theorem PhiG_KMap_eq_id (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (Waldhausen.KMap (P5NativePhi.Phi_exact X) n).comp
        (Waldhausen.KMap (P5NativeCoefficients.G_exact X) n) =
      MonoidHom.id ((FlasqueBoundedBelow.waldhausen (nativeLineFunctor.obj X).obj).K n) := by
  apply MonoidHom.ext
  intro a
  have h := PhiTwoSummandKMap_GPairKMap X n a
  change Waldhausen.KMap (P5NativePhi.Phi_exact X) n
    ((Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj)
      (FlasqueBoundedBelow.waldhausen X.obj) n).symm
      (Waldhausen.Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj)
        (FlasqueBoundedBelow.waldhausen X.obj) n
        (Waldhausen.KMap (P5NativeCoefficients.G_exact X) n a))) = a at h
  simpa only [MulEquiv.symm_apply_apply, MonoidHom.comp_apply, MonoidHom.id_apply] using h

/-- The actual geometric native G is a left inverse of the unchanged native Phi. -/
theorem nativeGeometricG_nativeTwoSummandKMap (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (a : PerfectK X.obj n × PerfectK X.obj n) :
    nativeGeometricG X n (nativeTwoSummandKMap X n a) = a := by
  obtain ⟨b, rfl⟩ := (modelProductInclusionKEquiv X n).surjective a
  rw [← PhiTwoSummandKMap_native_square, nativeGeometricG_model_apply,
    GPairKMap_PhiTwoSummandKMap]

/-- The actual geometric native G is a right inverse on every qcqs base. -/
theorem nativeTwoSummandKMap_nativeGeometricG (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a : PerfectK (nativeLineFunctor.obj X).obj n) :
    nativeTwoSummandKMap X n (nativeGeometricG X n a) = a := by
  obtain ⟨b, rfl⟩ := (modelInclusionKEquiv (nativeLineFunctor.obj X).obj n).surjective a
  rw [nativeGeometricG_model_apply, ← PhiTwoSummandKMap_native_square,
    PhiTwoSummandKMap_GPairKMap]

/-- Native G after the unchanged native two-summand homomorphism is the identity. -/
theorem nativeGeometricG_comp_nativeTwoSummandKMap (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (nativeGeometricG X n).comp (nativeTwoSummandKMap X n) =
      MonoidHom.id (PerfectK X.obj n × PerfectK X.obj n) :=
  MonoidHom.ext (nativeGeometricG_nativeTwoSummandKMap X n)

/-- The unchanged native two-summand homomorphism after native G is the identity. -/
theorem nativeTwoSummandKMap_comp_nativeGeometricG (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (nativeTwoSummandKMap X n).comp (nativeGeometricG X n) =
      MonoidHom.id (PerfectK (nativeLineFunctor.obj X).obj n) :=
  MonoidHom.ext (nativeTwoSummandKMap_nativeGeometricG X n)

/-- The existing native inverse is the transported actual original geometric pair G. -/
theorem nativeGlobalTwoSummandKEquiv_symm_apply (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (a : PerfectK (nativeLineFunctor.obj X).obj n) :
    (nativeGlobalTwoSummandKEquiv X n).symm a = nativeGeometricG X n a := by
  apply (nativeGlobalTwoSummandKEquiv X n).injective
  change nativeGlobalTwoSummandKEquiv X n ((nativeGlobalTwoSummandKEquiv X n).symm a) =
    nativeTwoSummandKMap X n (nativeGeometricG X n a)
  rw [MulEquiv.apply_symm_apply, nativeTwoSummandKMap_nativeGeometricG]

/-- The identification retains the literal existing native inverse homomorphism. -/
theorem nativeGlobalTwoSummandKEquiv_symm_toMonoidHom (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    (nativeGlobalTwoSummandKEquiv X n).symm.toMonoidHom = nativeGeometricG X n := by
  apply MonoidHom.ext
  intro a
  exact nativeGlobalTwoSummandKEquiv_symm_apply X n a

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeGlobal
