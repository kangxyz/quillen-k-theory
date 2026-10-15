/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.PolynomialLaurentNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationNaturality
public import Quillen.KTheory.Bass.DiagramTransport

/-!
# Original two-chart transport on the actual compact native coefficient row

The existing quasi-compact native row is compared by genuine natural
isomorphisms with the original polynomial and Laurent product functors. Both
original chart squares hold, including the inverse-coordinate map. Consequently
the actual two-chart contraction and its Laurent representatives transport for
any additive-group valued functor. Compactness of the original scheme is the
only geometric hypothesis.

This module supplies the original ambient coefficient maps and chart transport.
It does not claim supported-group comparisons, assembled scheme-restriction
naturality, seed invertibility, stabilization, telescope or TT identification.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
  AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The actual native polynomial/product isomorphism in the quasi-compact opposite row. -/
def boundedFlatCoefficientPolynomialIso :
    polynomialUnderFunctor R ⋙ boundedFlatCoefficientQuasiCompactRow P ≅
      boundedFlatCoefficientQuasiCompactRow P ⋙
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.op :=
  NatIso.ofComponents
    (fun a ↦ (AlgebraicGeometry.Scheme.quasiCompactSchemeProperty.isoMk (polynomialIso P
      a)).symm.op) (by
      intro a b g
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change (polynomialIso P b).inv ≫
        coefficientMap P ((polynomialUnderFunctor R).map g) =
          (AlgebraicGeometry.Scheme.Products.baseProductFunctor
            (PolynomialLaurent.polynomialProjection
              AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).map
              (coefficientMap P g) ≫ (polynomialIso P a).inv
      apply (cancel_mono (polynomialIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [polynomialIso_naturality P g, Iso.inv_hom_id_assoc])

/-- The actual native Laurent/product isomorphism in the same quasi-compact opposite row. -/
def boundedFlatCoefficientLaurentIso :
    laurentUnderFunctor R ⋙ boundedFlatCoefficientQuasiCompactRow P ≅
      boundedFlatCoefficientQuasiCompactRow P ⋙
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op :=
  NatIso.ofComponents
    (fun a ↦ (AlgebraicGeometry.Scheme.quasiCompactSchemeProperty.isoMk (laurentIso P a)).symm.op)
      (by
      intro a b g
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change (laurentIso P b).inv ≫
        coefficientMap P ((laurentUnderFunctor R).map g) =
          (AlgebraicGeometry.Scheme.Products.baseProductFunctor
            (PolynomialLaurent.laurentProjection
              AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).map
              (coefficientMap P g) ≫ (laurentIso P a).inv
      apply (cancel_mono (laurentIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [laurentIso_naturality P g, Iso.inv_hom_id_assoc])

/-- The forward opposite polynomial component is exactly the original geometric inverse. -/
@[simp] theorem boundedFlatCoefficientPolynomialIso_hom_app (a : Under R) :
    ((boundedFlatCoefficientPolynomialIso P).hom.app a).unop.hom =
      (polynomialIso P a).inv := rfl

/-- The forward opposite Laurent component is exactly the original geometric inverse. -/
@[simp] theorem boundedFlatCoefficientLaurentIso_hom_app (a : Under R) :
    ((boundedFlatCoefficientLaurentIso P).hom.app a).unop.hom =
      (laurentIso P a).inv := rfl

/-- The exact original positive square required by two-chart contraction transport. -/
@[reassoc] theorem boundedFlatCoefficientPolynomialLaurentIso_plus (a : Under R) :
    (boundedFlatCoefficientQuasiCompactRow P).map ((underToLaurent R).app a) ≫
        (boundedFlatCoefficientLaurentIso P).hom.app a =
      (boundedFlatCoefficientPolynomialIso P).hom.app a ≫
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus).app
          ((boundedFlatCoefficientQuasiCompactRow P).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentIso P a).inv ≫ laurentPlus P a =
    (AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
      (PolynomialLaurent.laurentPlus
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)
      (PolynomialLaurent.laurentPlus_projection
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).app
        (space (op P, a)) ≫ (polynomialIso P a).inv
  apply (cancel_mono (polynomialIso P a).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [polynomialLaurentIso_plus P a, Iso.inv_hom_id_assoc]

/-- The exact original inverse-coordinate square required by the same transport. -/
@[reassoc] theorem boundedFlatCoefficientPolynomialLaurentIso_minus (a : Under R) :
    (boundedFlatCoefficientQuasiCompactRow P).map ((underToLaurentInvert R).app a) ≫
        (boundedFlatCoefficientLaurentIso P).hom.app a =
      (boundedFlatCoefficientPolynomialIso P).hom.app a ≫
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus).app
          ((boundedFlatCoefficientQuasiCompactRow P).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentIso P a).inv ≫ laurentMinus P a =
    (AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
      (PolynomialLaurent.laurentMinus
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)
      (PolynomialLaurent.laurentMinus_projection
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).app
        (space (op P, a)) ≫ (polynomialIso P a).inv
  apply (cancel_mono (polynomialIso P a).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [polynomialLaurentIso_minus P a, Iso.inv_hom_id_assoc]

/-- Genuine original two-chart cokernel transport on the existing native coefficient row. -/
def boundedFlatCoefficientContractionTransportIso
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientQuasiCompactRow P ⋙ F) ≅
      boundedFlatCoefficientQuasiCompactRow P ⋙
        Quillen.Bass.TwoChart.contraction (NatTrans.op
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
          (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F :=
  Quillen.Bass.TwoChart.contractionTransportIso
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactRow P)
    (boundedFlatCoefficientPolynomialIso P) (boundedFlatCoefficientLaurentIso P)
    (boundedFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedFlatCoefficientPolynomialLaurentIso_minus P) F

/-- The same transport retains the original native Laurent quotient representative. -/
@[reassoc] theorem boundedFlatCoefficientContractionTransportIso_π
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactRow P ⋙ F)).app a ≫
        (boundedFlatCoefficientContractionTransportIso P F).hom.app a =
      F.map ((boundedFlatCoefficientLaurentIso P).hom.app a) ≫
        (Quillen.Bass.TwoChart.contractionπ (NatTrans.op
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
          (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F).app
            ((boundedFlatCoefficientQuasiCompactRow P).obj a) :=
  Quillen.Bass.TwoChart.contractionTransportIso_π
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactRow P)
    (boundedFlatCoefficientPolynomialIso P) (boundedFlatCoefficientLaurentIso P)
    (boundedFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedFlatCoefficientPolynomialLaurentIso_minus P) F a

end Quillen.PerfectComplexes
