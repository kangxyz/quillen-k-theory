/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.NativeLaurentClassComparison

/-! Public native consumers of the canonical Laurent-class comparison. -/

@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
universe u

namespace Consumer.NativeLaurentKOne

/-- The original native Bass map on a qc scheme has exactly the forward rank-one T class. -/
theorem forward_qc (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    perfectOpenKRestrict (plus.app X).hom 1
        (perfectScalarForwardKOneClass (plus.app X).hom
          (rankOnePerfect (polynomialFunctor.obj X).obj)
          (nativePolynomialCoordinate X.obj) (nativeLaurentUnit X.obj)
          (nativePolynomialCoordinate_laurentPlus X.obj)) =
      perfectGlobalUnitKOneClass (laurentFunctor.obj X).obj (nativeLaurentUnit X.obj)
        (rankOnePerfect (laurentFunctor.obj X).obj) :=
  nativeScalarForwardKOneClass_restrict_rankOne X.obj

/-- No quasi-compactness, affinity, or zero-component assumption is needed for the native client. -/
theorem cofiber_inverse (X : Scheme.{u}) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarCofiberBoundaryKOneClass (nativeLaurentPlus X)
          (rankOnePerfect (nativePolynomialScheme X))
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      (perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        (rankOnePerfect (nativeLaurentScheme X)))⁻¹ :=
  nativeScalarCofiberBoundaryKOneClass_restrict_rankOne X

end Consumer.NativeLaurentKOne
