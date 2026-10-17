/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairProjectedReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCapChartTripleWord
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareModelNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeTripleLaurentAnchor

/-! The actual polynomial source square meets the fixed right-first triple reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassReferenceMerge BassH0Merge
local notation "N" => boundedFlatNormalizedPullback
local notation "B" => BinaryNormalizationSimplex.total
private theorem small_refl {C₀ D₀ : Type u} [Category.{v} C₀] [Category.{v} D₀]
    (F : C₀ ⥤ D₀) : smallIso (Iso.refl F) = Iso.refl _ := by
  apply Iso.ext
  ext x
  rfl

private theorem small_eq_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (smallIso (eqToIso (congrArg N h)) :
      (normalizedMap f).functor ≅ (normalizedMap g).functor).symm =
      smallIso (eqToIso (congrArg N h.symm)) := rfl

private theorem associated_model_word {X Y Z U V W : Scheme.{u}}
    (l : X ⟶ Y) (k : Y ⟶ Z) (ja : Z ⟶ U) (jc : Y ⟶ V)
    (jd : X ⟶ W) (m : W ⟶ V) (h : V ⟶ U)
    (pt : W ⟶ U) (lt : X ⟶ Z) (ep : pt = m ≫ h) (el : lt = l ≫ k)
    (sq₁ : k ≫ ja = jc ≫ h) (sq₂ : l ≫ jc = jd ≫ m)
    (ht : lt ≫ ja = jd ≫ pt) :
    ((isoWhiskerRight (smallIso (eqToIso (congrArg N ep)) ≪≫ B m h)
        (normalizedMap jd).functor ≪≫
      (isoWhiskerLeft (normalizedMap h).functor
        ((B l jc).symm ≪≫ smallIso (eqToIso (congrArg N sq₂)) ≪≫ B jd m)).symm) ≪≫
      isoWhiskerRight ((B jc h).symm ≪≫
        smallIso (eqToIso (congrArg N sq₁.symm)) ≪≫ B k ja)
        (normalizedMap l).functor :
      (normalizedMap pt ≫ normalizedMap jd).functor ≅
        ((normalizedMap ja ≫ normalizedMap k) ≫ normalizedMap l).functor) =
    (B jd pt).symm ≪≫ smallIso (eqToIso (congrArg N ht.symm)) ≪≫ B lt ja ≪≫
      isoWhiskerLeft (normalizedMap ja).functor
        (smallIso (eqToIso (congrArg N el)) ≪≫ B l k) := by
  subst pt lt
  simpa only [eqToIso_refl, small_refl, Iso.refl_trans] using
    CoefficientBassCapChartTripleWord.model_word l k ja jc jd m h sq₁ sq₂ ht


variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original fourth polynomial-square node has its explicit full model endpoint. -/
def rightSquareIso : (sourceReference P p).functor ≅
    (normalizedMap (coefficientMap P p) ≫ normalizedMap (polynomialProjection P b)).functor :=
  NativeSquareModelNormalization.rightIso
    (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P p)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p)

/-- This is the prescribed seven-arrow word at the actual polynomial projection square. -/
theorem projection_word :
    (((isoWhiskerRight
        (smallIso (eqToIso (congrArg N
          (Category.assoc (coefficientMap P w) (coefficientMap P q)
            (coefficientMap P p)).symm)) ≪≫
          B (coefficientMap P w ≫ coefficientMap P q) (coefficientMap P p))
        (normalizedMap (polynomialProjection P d)).functor ≪≫
      (isoWhiskerLeft (normalizedMap (coefficientMap P p)).functor
        ((B (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
            coefficientMap P ((polynomialUnderFunctor R).map q)) (polynomialProjection P b)).symm ≪≫
          smallIso (eqToIso (congrArg N
            (PairLowerReference.polynomial_pair_naturality P q w).symm)) ≪≫
          B (polynomialProjection P d) (coefficientMap P w ≫ coefficientMap P q))).symm) ≪≫
      isoWhiskerRight
        ((B (polynomialProjection P b) (coefficientMap P p)).symm ≪≫
          smallIso (eqToIso (congrArg N
            (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm)) ≪≫
          B (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a))
        (pairReference P q w).functor) :
      (input P p q w ≫ normalizedMap (polynomialProjection P d)).functor ≅
        ((normalizedMap (polynomialProjection P a) ≫
          normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map p))) ≫
            pairReference P q w).functor) =
      (B (polynomialProjection P d)
        (coefficientMap P w ≫ coefficientMap P q ≫ coefficientMap P p)).symm ≪≫
      smallIso (eqToIso (congrArg N
        (CoefficientBassRaw1PolynomialSourceProjection.projection_total P p q w))) ≪≫
      B (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
        coefficientMap P ((polynomialUnderFunctor R).map q) ≫
          coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a) ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        (smallIso (eqToIso (congrArg N
          (Category.assoc (coefficientMap P ((polynomialUnderFunctor R).map w))
            (coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((polynomialUnderFunctor R).map p))).symm)) ≪≫
          B (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
            coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((polynomialUnderFunctor R).map p))) := by
  exact associated_model_word
    (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
      coefficientMap P ((polynomialUnderFunctor R).map q))
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P d)
    (coefficientMap P w ≫ coefficientMap P q) (coefficientMap P p)
    (coefficientMap P w ≫ coefficientMap P q ≫ coefficientMap P p)
    (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
      coefficientMap P ((polynomialUnderFunctor R).map q) ≫
        coefficientMap P ((polynomialUnderFunctor R).map p))
    (Category.assoc (coefficientMap P w) (coefficientMap P q) (coefficientMap P p)).symm
    (Category.assoc (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p))).symm
    (coefficientMap_naturality P (polynomialUnderCoefficient R) p)
    (PairLowerReference.polynomial_pair_naturality P q w).symm
    (CoefficientBassRaw1PolynomialSourceProjection.projection_total P p q w).symm

private theorem associator_refl {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃) :
    Functor.associator F G H = Iso.refl _ := by
  apply Iso.ext
  rfl

private theorem projection_cancel {V₀ V₁ V₂ V₃ V₄ V₅ : Model.{u}}
    (A : V₀ ⟶ V₁) (P : V₁ ⟶ V₃) (H : V₀ ⟶ V₂) (C : V₂ ⟶ V₃)
    (L : V₃ ⟶ V₅) (D : V₄ ⟶ V₅) (M : V₂ ⟶ V₄)
    (F : V₀ ⟶ V₄) (T : V₁ ⟶ V₅) (S : V₀ ⟶ V₃)
    (a : (F ≫ D).functor ≅ (A ≫ T).functor)
    (b : T.functor ≅ (P ≫ L).functor)
    (c : S.functor ≅ (A ≫ P).functor)
    (d : S.functor ≅ (H ≫ C).functor)
    (e : F.functor ≅ (H ≫ M).functor)
    (f : (M ≫ D).functor ≅ (C ≫ L).functor)
    (h : isoWhiskerRight e D.functor ≪≫ isoWhiskerLeft H.functor f ≪≫
      isoWhiskerRight (d.symm ≪≫ c) L.functor = a ≪≫ isoWhiskerLeft A.functor b) :
    (a ≪≫ isoWhiskerLeft A.functor b ≪≫
      (Functor.associator A.functor P.functor L.functor).symm ≪≫
      isoWhiskerRight c.symm L.functor) ≪≫ isoWhiskerRight d L.functor =
    isoWhiskerRight e D.functor ≪≫ Functor.associator H.functor M.functor D.functor ≪≫
      isoWhiskerLeft H.functor f ≪≫
      (Functor.associator H.functor C.functor L.functor).symm := by
  have hh := congrArg (fun k ↦ k ≪≫ isoWhiskerRight c.symm L.functor ≪≫
    isoWhiskerRight d L.functor) h.symm
  simp only [associator_refl, Iso.refl_symm, Iso.trans_assoc]
  erw [Iso.refl_trans, Iso.refl_trans, Iso.trans_refl]
  simpa only [Iso.trans_assoc, isoWhiskerRight_trans, ← isoWhiskerRight_symm,
    Iso.self_symm_id_assoc, Iso.symm_self_id, Iso.trans_refl] using hh

private theorem rightFirst_word {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.rightFirst f g h =
      smallIso (eqToIso (congrArg N (Category.assoc f g h).symm)) ≪≫ B (f ≫ g) h :=
  smallIso_trans _ _

private theorem rightSquareIso_word : rightSquareIso P p =
    smallIso (eqToIso (congrArg N
      (coefficientMap_naturality P (polynomialUnderCoefficient R) p))) ≪≫
        B (polynomialProjection P b) (coefficientMap P p) := by
  rw [rightSquareIso, NativeSquareModelNormalization.rightIso_original, smallIso_eqToIso]
  rfl

private theorem projectionIso_word :
    CoefficientBassRaw1PolynomialSourceProjection.polynomialIso P p q w =
      (B (polynomialProjection P d)
        (coefficientMap P w ≫ coefficientMap P q ≫ coefficientMap P p)).symm ≪≫
      smallIso (eqToIso (congrArg N
        (CoefficientBassRaw1PolynomialSourceProjection.projection_total P p q w))) ≪≫
      B (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
        coefficientMap P ((polynomialUnderFunctor R).map q) ≫
          coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a) := by
  rw [smallIso_eqToIso]
  rfl

/-- The complete fourth-node anchor is the original source-precomposed pair anchor. -/
theorem polynomial_anchor_node4 :
    polynomialAnchor P p q w ≪≫ isoWhiskerRight (rightSquareIso P p)
      (pairReference P q w).functor =
      isoWhiskerRight (TripleLaurent.inputIso P p q w)
          (normalizedMap (polynomialProjection P d)).functor ≪≫
        Functor.associator (normalizedMap (coefficientMap P p)).functor
          (inputReference P q w).functor (normalizedMap (polynomialProjection P d)).functor ≪≫
        isoWhiskerLeft (normalizedMap (coefficientMap P p)).functor
          (PairLowerReference.polynomialAnchor P q w) ≪≫
        (Functor.associator (normalizedMap (coefficientMap P p)).functor
          (normalizedMap (polynomialProjection P b)).functor
          (pairReference P q w).functor).symm := by
  apply projection_cancel
    (normalizedMap (polynomialProjection P a))
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (normalizedMap (coefficientMap P p)) (normalizedMap (polynomialProjection P b))
    (pairReference P q w) (normalizedMap (polynomialProjection P d))
    (inputReference P q w) (input P p q w)
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w) (sourceReference P p)
    (CoefficientBassRaw1PolynomialSourceProjection.polynomialIso P p q w)
    (NormalizedTripleSimplex.rightFirst
      (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (B (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a))
    (rightSquareIso P p) (TripleLaurent.inputIso P p q w)
    (PairLowerReference.polynomialAnchor P q w)
  have h := projection_word P p q w
  rw [projectionIso_word, rightFirst_word, TripleLaurent.inputIso_small, smallIso_trans,
    PairLowerReference.polynomial_anchor_normalized, rightSquareIso_word]
  rw [← small_eq_symm (coefficientMap_naturality P (polynomialUnderCoefficient R) p),
    ← small_eq_symm (PairLowerReference.polynomial_pair_naturality P q w)] at h
  simpa only [Iso.trans_assoc, Iso.trans_symm, isoWhiskerRight_trans,
    isoWhiskerLeft_symm, Iso.symm_symm_eq, BinaryNormalizationSimplex.total, smallIso] using h

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
