/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.NativeCoordinates


public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Relative

/-! The actual relative Laurent-unit K-one comparison over every base scheme.
Both schemes are the original products over the integral terminal scheme. The coordinate
and unit come from their second projections; no affine replacement of the base is used. -/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Bass

end AlgebraicGeometry.Scheme.Bass

namespace Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.Bass

/-- Every perfect object over the true relative affine line has the original unit comparison. -/
theorem nativeScalarForwardKOneClass_restrict (X : Scheme.{u})
    (K : Perfect (nativePolynomialScheme X)) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarForwardKOneClass (nativeLaurentPlus X) K
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        ((perfectRestrict (nativeLaurentPlus X)).obj K) :=
  perfectScalarForwardKOneClass_restrict _ _ _ _ _

/-- The normalized forward square restricts to [T] on the genuine rank-one structure sheaf. -/
theorem nativeScalarForwardKOneClass_restrict_rankOne (X : Scheme.{u}) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarForwardKOneClass (nativeLaurentPlus X)
          (rankOnePerfect (nativePolynomialScheme X))
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        (rankOnePerfect (nativeLaurentScheme X)) :=
  perfectScalarForwardKOneClass_restrict_rankOne _ _ _ _

/-- The cofiber boundary keeps its accepted inverse orientation on every relative Laurent open. -/
theorem nativeScalarCofiberBoundaryKOneClass_restrict_rankOne (X : Scheme.{u}) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarCofiberBoundaryKOneClass (nativeLaurentPlus X)
          (rankOnePerfect (nativePolynomialScheme X))
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      (perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        (rankOnePerfect (nativeLaurentScheme X)))⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_restrict_rankOne _ _ _ _

end Quillen.PerfectComplexes
