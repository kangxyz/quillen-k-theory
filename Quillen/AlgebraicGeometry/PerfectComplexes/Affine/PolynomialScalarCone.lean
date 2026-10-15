/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenScalarUnit
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialCoordinate

/-!
# The original polynomial scalar cone on the Laurent open

Multiplication by the original polynomial coordinate becomes precisely the original Laurent
unit after restriction. Its literal mapping cone therefore defines a supported perfect object
and its canonical fiber loop. Identifying the localization boundary of the Laurent automorphism
with this specified fiber loop remains a separate comparison.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.Affine

/-- The literal cone of multiplication by the original polynomial coordinate, supported on X=0.
-/
def polynomialScalarCone (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    AcyclicCategory (perfectOpenNested (laurentPlus R)) :=
  perfectOpenScalarCone (laurentPlus R) (polynomialGlobalCoordinate R) (laurentGlobalUnit R)
    (polynomialGlobalCoordinate_laurentPlus R) K

/-- The canonical fiber loop retains the original supported cone and reversed zero track. -/
def polynomialScalarConeFiberLoop (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :=
  canonicalFiberObjectLoop (perfectOpenNested (laurentPlus R)) (polynomialScalarCone R K)

/-- The cone complex is exactly the cone of the original polynomial scalar endomorphism. -/
theorem polynomialScalarCone_original (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (polynomialScalarCone R K).obj.obj =
      CochainComplex.mappingCone ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app
        K.obj) := rfl

/-- The fiber path keeps the independent original nullhomotopy and object-loop coordinates. -/
theorem polynomialScalarConeFiberLoop_path (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) (t s : unitInterval) :
    (polynomialScalarConeFiberLoop R K t).val.2 s =
      acyclicNullhomotopy (perfectOpenNested (laurentPlus R))
        (s, (acyclicStructure (perfectOpenNested (laurentPlus R))).kZeroObjectLoop
          (polynomialScalarCone R K) t) := rfl

end Quillen.PerfectComplexes.Affine
