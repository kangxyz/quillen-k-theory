/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeContractionCorner
public import Quillen.KTheory.Bass.TwoChartAdditive
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Interchanging contraction with the original scheme Bass middle row

The actual independent polynomial and Laurent product swaps identify contraction of the
original common-corner and signed chart-difference row with the same row of the contracted
functor. The comparison preserves both original chart maps and the original projection. It
asserts no exactness for an arbitrary row and identifies no boundary with a quotient projection.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u w
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart

variable (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})

/-- The unchanged common projection and signed chart difference as a natural short complex. -/
def bassMiddleComplex : ShortComplex (QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  ShortComplex.mk
    (biprod.lift (Functor.whiskerRight (NatTrans.op polynomialProjection) F)
      (Functor.whiskerRight (NatTrans.op polynomialProjection) F))
    (biprod.desc (Functor.whiskerRight (NatTrans.op plus) F)
      (-Functor.whiskerRight (NatTrans.op minus) F)) (by
    rw [biprod.lift_desc, Preadditive.comp_neg]
    have h : Functor.whiskerRight (NatTrans.op polynomialProjection) F ≫
        Functor.whiskerRight (NatTrans.op plus) F =
      Functor.whiskerRight (NatTrans.op polynomialProjection) F ≫
        Functor.whiskerRight (NatTrans.op minus) F := by
      apply NatTrans.ext
      funext X
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      apply congrArg F.map
      apply Quiver.Hom.unop_inj
      exact (plus_projection X.unop).trans (minus_projection X.unop).symm
    rw [h, add_neg_cancel])

/-- The genuine product transport preserves the original positive chart after contraction. -/
@[reassoc]
theorem productContractionTransportIso_plus :
    (contractionFunctor (NatTrans.op plus) (NatTrans.op minus)).map
        (Functor.whiskerRight (NatTrans.op plus) F) ≫
      (productContractionTransportIso
        (PolynomialLaurent.laurentProjection integerRing) F).hom =
    (productContractionTransportIso
      (PolynomialLaurent.polynomialProjection integerRing) F).hom ≫
        Functor.whiskerRight (NatTrans.op plus)
          (contraction (NatTrans.op plus) (NatTrans.op minus) F) := by
  apply NatTrans.ext
  funext X
  exact productContractionTransportIso_factorMap
    (PolynomialLaurent.laurentProjection integerRing)
    (PolynomialLaurent.polynomialProjection integerRing)
    (PolynomialLaurent.laurentPlus integerRing)
    (PolynomialLaurent.laurentPlus_projection integerRing) F X

/-- The same product transport retains the original inverse-coordinate chart. -/
@[reassoc]
theorem productContractionTransportIso_minus :
    (contractionFunctor (NatTrans.op plus) (NatTrans.op minus)).map
        (Functor.whiskerRight (NatTrans.op minus) F) ≫
      (productContractionTransportIso
        (PolynomialLaurent.laurentProjection integerRing) F).hom =
    (productContractionTransportIso
      (PolynomialLaurent.polynomialProjection integerRing) F).hom ≫
        Functor.whiskerRight (NatTrans.op minus)
          (contraction (NatTrans.op plus) (NatTrans.op minus) F) := by
  apply NatTrans.ext
  funext X
  exact productContractionTransportIso_factorMap
    (PolynomialLaurent.laurentProjection integerRing)
    (PolynomialLaurent.polynomialProjection integerRing)
    (PolynomialLaurent.laurentMinus integerRing)
    (PolynomialLaurent.laurentMinus_projection integerRing) F X

/-- Actual independent-variable interchange on all three objects and both original middle maps.
-/
def contractionBassMiddleIso :
    (bassMiddleComplex F).map
        (contractionFunctor (NatTrans.op plus) (NatTrans.op minus)) ≅
      bassMiddleComplex (contraction (NatTrans.op plus) (NatTrans.op minus) F) := by
  let B := contractionFunctor (NatTrans.op plus) (NatTrans.op minus)
  let : PreservesBinaryBiproducts B := preservesBinaryBiproducts_of_preservesBinaryProducts B
  let eP : B.obj (polynomialFunctor.op ⋙ F) ≅ polynomialFunctor.op ⋙ B.obj F :=
    productContractionTransportIso
    (PolynomialLaurent.polynomialProjection integerRing) F
  let eL : B.obj (laurentFunctor.op ⋙ F) ≅ laurentFunctor.op ⋙ B.obj F :=
    productContractionTransportIso
    (PolynomialLaurent.laurentProjection integerRing) F
  let c := Functor.whiskerRight (NatTrans.op polynomialProjection) F
  let p := Functor.whiskerRight (NatTrans.op plus) F
  let m := Functor.whiskerRight (NatTrans.op minus) F
  have hc : B.map c ≫ eP.hom =
      Functor.whiskerRight (NatTrans.op polynomialProjection) (B.obj F) := by
    apply NatTrans.ext
    funext X
    exact productContractionTransportIso_polynomialProjection F X
  refine ShortComplex.isoMk (Iso.refl _)
    ((B.mapBiprod (polynomialFunctor.op ⋙ F) (polynomialFunctor.op ⋙ F)) ≪≫
      biprod.mapIso eP eP) eL ?_ ?_
  · change 𝟙 _ ≫ biprod.lift _ _ =
      B.map (biprod.lift c c) ≫ (B.mapBiprod _ _).hom ≫ biprod.map eP.hom eP.hom
    rw [Category.id_comp, ← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst, biprod.lift_snd, biprod.lift_fst_assoc,
        biprod.lift_snd_assoc, hc] <;> rfl
  · change ((B.mapBiprod _ _).hom ≫ biprod.map eP.hom eP.hom) ≫
        biprod.desc _ _ = B.map (biprod.desc p (-m)) ≫ eL.hom
    apply (cancel_epi (B.mapBiprod (polynomialFunctor.op ⋙ F)
      (polynomialFunctor.op ⋙ F)).inv).mp
    rw [← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ← Category.assoc, biprod.mapBiprod_inv_map_desc, Functor.map_neg]
    apply biprod.hom_ext'
    · simpa only [Category.assoc, biprod.inl_map_assoc, biprod.inl_desc_assoc,
        biprod.inl_desc] using (productContractionTransportIso_plus F).symm
    · simpa only [Category.assoc, biprod.inr_map_assoc, biprod.inr_desc_assoc,
        biprod.inr_desc, Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg (productContractionTransportIso_minus F).symm

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
