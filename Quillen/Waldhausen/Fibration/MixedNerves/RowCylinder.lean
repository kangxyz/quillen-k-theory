/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Fibration.MixedNerves.Cylinder
public import Quillen.Waldhausen.Fibration.Rows.TrivialCofibrationCylinder

/-! # The original quotient-row cylinder on fine-weak chains

The genuine row middle functor preserves fine squares by its accepted
exactness. Thus the pointwise chain cylinder applies to the same original
quotient-row objects, with the original row cofibrations and coarse maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)

/-- Actual fine-square preservation of the original row cylinder. -/
theorem rowCylinder_fineSquares (n : SimplexCategory) :
    CylinderPreservesFineSquares (RowWeakEquivalences.nested N n)
      (RowFactorization.trivialCofibrationCylinder N D hs n) :=
  RowFactorization.factorization_fineSquares N D n

/-- The genuine pointwise cylinder on fine-weak chains of original quotient rows. -/
def rowChainCylinder (n k : SimplexCategory) :
    TrivialCofibrations.CylinderData
      (pointwiseCof (QuotientRows.waldhausenStructure V n) k)
      (pointwiseCoarse (RowWeakEquivalences.nested N n) k) :=
  chainCylinder (RowWeakEquivalences.nested N n)
    (RowFactorization.trivialCofibrationCylinder N D hs n) (rowCylinder_fineSquares N D hs n) k

@[simp] theorem rowChainCylinder_projection_app (n k : SimplexCategory)
    (f : Arrow (FineChain (QuotientRows.waldhausenStructure V n) k))
    (i : Fin (k.len + 1)) (p : Interval n) :
    (((rowChainCylinder N D hs n k).projection.app f).hom.app i).hom.app p =
      D.projection.app (Arrow.mk ((f.hom.hom.app i).hom.app p)) := rfl

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The actual complex cylinder gives the required fine-chain data without extra inputs. -/
def complexRowChainCylinder (n k : SimplexCategory) :=
  rowChainCylinder (complexSubcategoryNested P) (complexJointData P hcone hshift)
    (complexJointData_secondEndpointSection P hcone hshift) n k

end Quillen.Waldhausen.Fibration.MixedNerves
