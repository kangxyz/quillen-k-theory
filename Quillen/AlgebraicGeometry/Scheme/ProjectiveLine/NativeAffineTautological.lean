/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalCoefficientPullback
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.NativeBaseChange

/-!
# Original native affine tautological-line identification

The actual affine scheme comparison preserves the original integer projection.
Arbitrary coefficient pullback of the original integer line identifies its
native tautological pullback with the actual two-chart tautological line.
-/
@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Bass

namespace AlgebraicGeometry.Scheme.ProjectiveLine

/-- The actual native affine comparison retains the original tautological line. -/
def nativeAffineTautologicalIso (R : CommRingCat.{u}) :
    (Scheme.Modules.pullback (nativeAffineIso R).hom).obj
        (nativeTautologicalLine ⟨Spec R, inferInstance⟩) ≅ tautologicalLine R :=
  (Scheme.Modules.pullbackComp (nativeAffineIso R).hom
      (nativeIntegerProjection ⟨Spec R, inferInstance⟩)).app (tautologicalLine integerRing) ≪≫
    (Scheme.Modules.pullbackCongr (nativeAffineIso_integerProjection R)).app _ ≪≫
    tautologicalCoefficientIso (integerMap R)

end AlgebraicGeometry.Scheme.ProjectiveLine
