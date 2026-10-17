/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurentSchemeNaturality
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientOpenRestriction
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OpenPairs
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialLaurentTransport

/-!
# Original polynomial and Laurent transport for native coefficient open pairs

An open immersion over the fixed base defines a functor of actual open pairs on
all coefficient algebras. The original native polynomial and Laurent product
isomorphisms lift to these pairs, preserving both chart maps. This supplies the
actual two-chart contraction transport, including its original Laurent quotient.
Only compactness of the ambient scheme is needed for this geometric interface.
The subsequent supported finite-bottom comparison has separate K-zero input.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
universe u w
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The unchanged native open pairs and all original coefficient squares, with qc ambient. -/
def boundedFlatCoefficientQuasiCompactOpenPairRow : Under R ⥤ QuasiCompactOpenPairs.{u}ᵒᵖ where
  obj a := op ⟨boundedFlatCoefficientOpenPair f a, compactSpace_space (op Q, a)⟩
  map g := (ObjectProperty.homMk (boundedFlatCoefficientOpenPairMap f g)).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op Q, a)
  map_comp {a b c} g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact coefficientMap_comp P g h
    · exact coefficientMap_comp Q g h

/-- Forgetting the removed open gives exactly the original compact ambient coefficient row. -/
theorem boundedFlatCoefficientQuasiCompactOpenPairRow_base :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ quasiCompactOpenPairsBase.op =
      boundedFlatCoefficientQuasiCompactRow Q := rfl

/-- The original polynomial product comparison as an isomorphism of actual open pairs. -/
def boundedFlatCoefficientOpenPairPolynomialIso (a : Under R) :
    ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj
      ((polynomialUnderFunctor R).obj a)).unop ≅
      Scheme.Bass.pairPolynomialFunctor.obj
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop :=
  quasiCompactOpenPairProperty.isoMk (openPairProperty.isoMk
    (Arrow.isoMk (polynomialIso P a) (polynomialIso Q a) (polynomialIso_schemeMap f a).symm))

/-- The same actual polynomial pair isomorphisms are natural in every coefficient arrow. -/
def boundedFlatCoefficientSupportedPolynomialIso :
    polynomialUnderFunctor R ⋙ boundedFlatCoefficientQuasiCompactOpenPairRow f ≅
      boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Scheme.Bass.pairPolynomialFunctor.op :=
  NatIso.ofComponents (fun a ↦ (boundedFlatCoefficientOpenPairPolynomialIso f a).symm.op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · change (polynomialIso P b).inv ≫
        coefficientMap P ((polynomialUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.polynomialProjection
              Scheme.PolynomialLaurent.Relative.integerRing)).map (coefficientMap P g) ≫
                (polynomialIso P a).inv
      apply (cancel_mono (polynomialIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [polynomialIso_naturality P g, Iso.inv_hom_id_assoc]
    · change (polynomialIso Q b).inv ≫
        coefficientMap Q ((polynomialUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.polynomialProjection
              Scheme.PolynomialLaurent.Relative.integerRing)).map (coefficientMap Q g) ≫
                (polynomialIso Q a).inv
      apply (cancel_mono (polynomialIso Q a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [polynomialIso_naturality Q g, Iso.inv_hom_id_assoc])

/-- The original laurent product comparison as an isomorphism of actual open pairs. -/
def boundedFlatCoefficientOpenPairLaurentIso (a : Under R) :
    ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj
      ((laurentUnderFunctor R).obj a)).unop ≅
      Scheme.Bass.pairLaurentFunctor.obj
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop :=
  quasiCompactOpenPairProperty.isoMk (openPairProperty.isoMk
    (Arrow.isoMk (laurentIso P a) (laurentIso Q a) (laurentIso_schemeMap f a).symm))

/-- The same actual laurent pair isomorphisms are natural in every coefficient arrow. -/
def boundedFlatCoefficientSupportedLaurentIso :
    laurentUnderFunctor R ⋙ boundedFlatCoefficientQuasiCompactOpenPairRow f ≅
      boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Scheme.Bass.pairLaurentFunctor.op :=
  NatIso.ofComponents (fun a ↦ (boundedFlatCoefficientOpenPairLaurentIso f a).symm.op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · change (laurentIso P b).inv ≫
        coefficientMap P ((laurentUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.laurentProjection
              Scheme.PolynomialLaurent.Relative.integerRing)).map (coefficientMap P g) ≫
                (laurentIso P a).inv
      apply (cancel_mono (laurentIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [laurentIso_naturality P g, Iso.inv_hom_id_assoc]
    · change (laurentIso Q b).inv ≫
        coefficientMap Q ((laurentUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.laurentProjection
              Scheme.PolynomialLaurent.Relative.integerRing)).map (coefficientMap Q g) ≫
                (laurentIso Q a).inv
      apply (cancel_mono (laurentIso Q a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [laurentIso_naturality Q g, Iso.inv_hom_id_assoc])

/-- The actual supported plus chart square, before applying any K-theory functor. -/
@[reassoc] theorem boundedFlatCoefficientSupportedPolynomialLaurentIso_plus (a : Under R) :
    (boundedFlatCoefficientQuasiCompactOpenPairRow f).map ((underToLaurent R).app a) ≫
        (boundedFlatCoefficientSupportedLaurentIso f).hom.app a =
      (boundedFlatCoefficientSupportedPolynomialIso f).hom.app a ≫
        (NatTrans.op Scheme.Bass.pairPlus).app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · change (laurentIso P a).inv ≫ laurentPlus P a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentPlus Scheme.PolynomialLaurent.Relative.integerRing)
        (PolynomialLaurent.laurentPlus_projection
          Scheme.PolynomialLaurent.Relative.integerRing)).app (space (op P, a)) ≫
            (polynomialIso P a).inv
    apply (cancel_mono (polynomialIso P a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_plus P a, Iso.inv_hom_id_assoc]
  · change (laurentIso Q a).inv ≫ laurentPlus Q a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentPlus Scheme.PolynomialLaurent.Relative.integerRing)
        (PolynomialLaurent.laurentPlus_projection
          Scheme.PolynomialLaurent.Relative.integerRing)).app (space (op Q, a)) ≫
            (polynomialIso Q a).inv
    apply (cancel_mono (polynomialIso Q a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_plus Q a, Iso.inv_hom_id_assoc]

/-- The actual supported minus chart square, before applying any K-theory functor. -/
@[reassoc] theorem boundedFlatCoefficientSupportedPolynomialLaurentIso_minus (a : Under R) :
    (boundedFlatCoefficientQuasiCompactOpenPairRow f).map ((underToLaurentInvert R).app a) ≫
        (boundedFlatCoefficientSupportedLaurentIso f).hom.app a =
      (boundedFlatCoefficientSupportedPolynomialIso f).hom.app a ≫
        (NatTrans.op Scheme.Bass.pairMinus).app
          ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext
  · change (laurentIso P a).inv ≫ laurentMinus P a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentMinus Scheme.PolynomialLaurent.Relative.integerRing)
        (PolynomialLaurent.laurentMinus_projection
          Scheme.PolynomialLaurent.Relative.integerRing)).app (space (op P, a)) ≫
            (polynomialIso P a).inv
    apply (cancel_mono (polynomialIso P a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_minus P a, Iso.inv_hom_id_assoc]
  · change (laurentIso Q a).inv ≫ laurentMinus Q a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentMinus Scheme.PolynomialLaurent.Relative.integerRing)
        (PolynomialLaurent.laurentMinus_projection
          Scheme.PolynomialLaurent.Relative.integerRing)).app (space (op Q, a)) ≫
            (polynomialIso Q a).inv
    apply (cancel_mono (polynomialIso Q a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_minus Q a, Iso.inv_hom_id_assoc]

/-- Genuine original two-chart cokernel transport on the existing native coefficient row. -/
def boundedFlatCoefficientSupportedContractionTransportIso
    (F : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Quillen.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ F) ≅
      boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙
        Quillen.Bass.TwoChart.contraction (NatTrans.op
          Scheme.Bass.pairPlus)
          (NatTrans.op Scheme.Bass.pairMinus) F :=
  Quillen.Bass.TwoChart.contractionTransportIso
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op
      Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactOpenPairRow f)
    (boundedFlatCoefficientSupportedPolynomialIso f) (boundedFlatCoefficientSupportedLaurentIso f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_minus f) F

/-- The same transport retains the original native Laurent quotient representative. -/
@[reassoc] theorem boundedFlatCoefficientSupportedContractionTransportIso_π
    (F : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ F)).app a ≫
        (boundedFlatCoefficientSupportedContractionTransportIso f F).hom.app a =
      F.map ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
        (Quillen.Bass.TwoChart.contractionπ (NatTrans.op
          Scheme.Bass.pairPlus)
          (NatTrans.op Scheme.Bass.pairMinus) F).app
            ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) :=
  Quillen.Bass.TwoChart.contractionTransportIso_π
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op
      Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientQuasiCompactOpenPairRow f)
    (boundedFlatCoefficientSupportedPolynomialIso f) (boundedFlatCoefficientSupportedLaurentIso f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedFlatCoefficientSupportedPolynomialLaurentIso_minus f) F a

end Quillen.PerfectComplexes
