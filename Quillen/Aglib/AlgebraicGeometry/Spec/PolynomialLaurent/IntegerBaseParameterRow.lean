/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseSpecSquare
public import Quillen.Aglib.AlgebraicGeometry.Products.IntegerBaseCoefficientRow

/-! # The whole geometric Spec row and its original unit

The intended upstream module is
`Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseParameterRow`.
The row uses an arbitrary scheme over `Spec (CommRingCat.of (ULift.{u} ℤ))`,
arbitrary coefficient algebras under `CommRingCat.of (ULift.{u} ℤ)`, and their
original morphisms. The unit statement accepts every global unit of the coefficient
spectrum. The current production consumer is
`Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseCanonicalRow`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

/-- Parameter-first products and the original coefficient fibers form isomorphic rows. -/
def parameterRowIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ (baseProductFunctor Q.hom).op ≅
      row Q ⋙ functor (CommRingCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun a => (rowIso Q a).op) (fun f =>
    Quiver.Hom.unop_inj (rowIso_coefficient Q f).symm)

/-- The row isomorphism preserves the actual restriction arrow of the fixed pair. -/
theorem parameterRowIso_scheme {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((baseProductTransformation P.hom Q.hom f.left (Over.w f)).app (Spec a.right)).op ≫
        (parameterRowIso P).hom.app a =
      (parameterRowIso Q).hom.app a ≫ (schemeMap f a).op :=
  Quiver.Hom.unop_inj (rowIso_scheme f a).symm

/-- Symmetry preserves the complete coefficient unit, with no coordinate inversion. -/
theorem rowIso_unit (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (v : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (rowIso Q a).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.fst (toIntegerBase (Spec a.right)) Q.hom).appTop.hom.toMonoidHom v) =
      Units.map (coefficientProjection (op Q, a)).appTop.hom.toMonoidHom v := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (rowIso_fst Q a)
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑v)

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
