/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBinaryUnion
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeFiniteCoverInduction

/-! # The original native projective-line K-map on qcqs schemes

Actual affine P4, isomorphism invariance and the original Mayer–Vietoris
five-term ladder discharge all premises of finite affine-cover induction.
The resulting equivalence retains the existing native two-summand K-map,
its product coordinates and every original connective degree, including zero.
Identification of its inverse with the geometric coefficient pair is separate.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u

namespace Quillen.PerfectComplexes.ProjectiveLine
open Quillen.Scheme Quillen.Scheme.ProjectiveLine

/-- The actual original native comparison holds on every qcqs scheme. -/
theorem nativePhiBijective_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : NativePhiBijective X :=
  NativeFiniteCoverInduction.of_qcqs NativePhiBijective
    nativePhiBijective_of_iso nativePhiBijective_of_isAffine
    (fun {Y} _ => nativePhiBijective_union Y) X

/-- The unchanged native two-summand K-map is bijective, including degree zero. -/
theorem nativeTwoSummandKMap_qcqs_bijective (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    Function.Bijective (nativeTwoSummandKMap X n) :=
  nativePhiBijective_of_qcqs X.obj X.property n

/-- The native qcqs equivalence has the literal existing forward map. -/
def nativeGlobalTwoSummandKEquiv (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    PerfectK X.obj n × PerfectK X.obj n ≃* PerfectK (nativeLineFunctor.obj X).obj n :=
  MulEquiv.ofBijective (nativeTwoSummandKMap X n)
    (nativeTwoSummandKMap_qcqs_bijective X n)

lemma nativeGlobalTwoSummandKEquiv_apply (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) (x : PerfectK X.obj n × PerfectK X.obj n) :
    nativeGlobalTwoSummandKEquiv X n x = nativeTwoSummandKMap X n x := rfl

end Quillen.PerfectComplexes.ProjectiveLine
