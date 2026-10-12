/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.IdentityCofiberNormalization
public import Quillen.Waldhausen.Fibration.CanonicalFiberComponentTranslation
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFiberBoundaryPath
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberBoundaryOrientation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-!
# Original polynomial scalar classes under component normalization

The same actual scalar and canonical-fiber loops can be normalized with either the original
identity-cofiber triangle or the existing standard suffix. These class equalities do not
identify either class with a separate prespectrum Laurent-unit construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.Tests.PolynomialScalarComponentNormalization
variable (R : CommRingCat.{u}) (K : Perfect (Spec (.of (Polynomial R))))
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested (laurentPlus R))

/-- The actual scalar-cofiber loop has the same class under both prescribed normalizations. -/
theorem original_boundary_normalization :
    ((W).identityCofiberComponentEquiv K 1).symm
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk
          (perfectScalarCofiberBoundaryLoop (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K))) =
      (loopLeftComponentHomotopyEquiv ((W).kZeroObjectLoop K) 1).symm
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk
          (perfectScalarCofiberBoundaryLoop (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K))) := by
  rw [(W).identityCofiberComponentEquiv_eq K]

/-- The original forward-T weak-arrow loop retains its class under the same normalization change.
-/
theorem original_forward_scalar_normalization :
    ((W).identityCofiberComponentEquiv K 1).symm
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk
          (perfectScalarWeakLoop (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K))) =
      (loopLeftComponentHomotopyEquiv ((W).kZeroObjectLoop K) 1).symm
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk
          (perfectScalarWeakLoop (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K))) := by
  rw [(W).identityCofiberComponentEquiv_eq K]

/-- The genuine fiber equivalence retains the exact original transposed canonical-fiber point. -/
theorem original_fiber_translation :
    canonicalFiberComponentEquiv (perfectOpenNested (laurentPlus R)) K
        (canonicalFiberObjectLoopTranspose (perfectOpenNested (laurentPlus R))
          (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)) =
      canonicalFiberObjectPrefixTransport (perfectOpenNested (laurentPlus R)) K
        (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K) :=
  canonicalFiberComponentEquiv_object _ _ _

/-- The explicit original iterated-fiber path terminates at that same prescribed fiber point. -/
theorem original_fiber_path_target :
    perfectScalarCofiberFiberBoundaryPath (laurentPlus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K 1 =
      canonicalFiberObjectPrefixTransport (perfectOpenNested (laurentPlus R)) K
        (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K) :=
  (perfectScalarCofiberFiberBoundaryPath (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K).target

end Quillen.Tests.PolynomialScalarComponentNormalization
