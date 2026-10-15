/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiber
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PolynomialScalarCone

/-! # The original polynomial scalar extension and supported cofiber consumers -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen
open Quillen.Waldhausen.SplitFactorization

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes.Affine AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.Waldhausen.Fibration
universe u
namespace QuillenTest.PolynomialScalarCofiber

open Quillen

/-- The actual universal cofiber is identified with the unchanged supported polynomial cone. -/
def originalScalarCofiberIso (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (ExtensionCategory.cofiber (perfectWaldhausen (Spec (.of (Polynomial R))))).obj
        (perfectScalarExtension _ (polynomialGlobalCoordinate R) K) ≅
      (polynomialScalarCone R K).obj :=
  perfectOpenScalarCofiberIso (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K

/-- The original quotient intertwines with the explicit signed mapping-cone quotient. -/
theorem original_quotient (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (ExtensionCategory.quotient (perfectWaldhausen (Spec (.of (Polynomial R))))).app
        (perfectScalarExtension _ (polynomialGlobalCoordinate R) K) ≫
      (originalScalarCofiberIso R K).hom =
        (locallyPerfect (Spec (.of (Polynomial R)))).homMk
          (quotientToCone ((complexGlobalScalar _ (polynomialGlobalCoordinate R)).app K.obj)) :=
  perfectOpenScalarCofiberIso_quotient (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K

/-- The original target summand still enters the unchanged mapping cone by its original inclusion.
-/
theorem original_target_inclusion {A : Type u} [Category.{u} A] [Abelian A]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (biprod.inr : L ⟶ middle f) ≫ quotientToCone f = CochainComplex.mappingCone.inr f := by
  rw [quotientToCone, ← Category.assoc]
  simp only [quotientMap, biprod.inr_desc]
  exact Quillen.CochainComplex.mappingConeNegIso_inr f

/-- The two genuine relative-acyclic objects have their original common K₀ class. -/
theorem original_acyclic_class (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    (acyclicStructure (perfectOpenNested (laurentPlus R))).kZeroObjectClass
        (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K) =
      (acyclicStructure (perfectOpenNested (laurentPlus R))).kZeroObjectClass
        (polynomialScalarCone R K) :=
  perfectOpenScalarCofiberAcyclic_class (laurentPlus R) (polynomialGlobalCoordinate R)
    (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K

/-- The same class equality survives the unchanged original canonical fiber map. -/
theorem original_canonical_fiber_class (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    canonicalFiberKMap (perfectOpenNested (laurentPlus R)) 0
        ((acyclicStructure (perfectOpenNested (laurentPlus R))).kZeroObjectClass
          (perfectOpenScalarCofiberAcyclic (laurentPlus R) (polynomialGlobalCoordinate R)
            (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R) K)) =
      canonicalFiberKMap (perfectOpenNested (laurentPlus R)) 0
        ((acyclicStructure (perfectOpenNested (laurentPlus R))).kZeroObjectClass
          (polynomialScalarCone R K)) :=
  congrArg (canonicalFiberKMap (perfectOpenNested (laurentPlus R)) 0)
    (original_acyclic_class R K)

end QuillenTest.PolynomialScalarCofiber
