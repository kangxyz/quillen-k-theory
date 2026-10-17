/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomialNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairLowerReference

/-! Full lower product nodes of the prescribed finite-source polynomial input cap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct

private theorem reanchor_node {V W T : Model.{v}} (D : V ⟶ W) (F : W ⟶ T)
    (G H : V ⟶ T) (a : G.functor ≅ H.functor) (b : H.functor ≅ (D ≫ F).functor)
    (N : Node D) (M : Node F) :
    reanchor a (node H D F b N M) = node G D F (a ≪≫ b) N M := by
  simp only [reanchor, node, Iso.trans_assoc]

/-- The two lower-product associations retain both complete reference isomorphisms. -/
theorem lower_product_node {V W T U X : Model.{v}}
    (D : V ⟶ W) (F : W ⟶ T) (J : T ⟶ U) (C : W ⟶ X) (L : X ⟶ U)
    (G : V ⟶ U) (a : G.functor ≅ ((D ≫ F) ≫ J).functor)
    (l : (F ≫ J).functor ≅ (C ≫ L).functor) (N : Node D) (M : Node L) :
    reanchor a (node ((D ≫ F) ≫ J) D (F ≫ J)
      (Functor.associator D.functor F.functor J.functor) N
      (reanchor l (precompNode C M))) =
    node G (D ≫ C) L
      (a ≪≫ Functor.associator D.functor F.functor J.functor ≪≫
        isoWhiskerLeft D.functor l ≪≫ (Functor.associator D.functor C.functor L.functor).symm)
      (postcompNode C N) M := by
  rw [reanchor_node, node_second_reanchor]
  have ha : Functor.associator D.functor C.functor L.functor = Iso.refl _ := rfl
  simp only [ha, Iso.refl_symm, ← Iso.trans_assoc]
  erw [Iso.trans_refl, Iso.trans_refl]
  simpa only [preNode, postNode, reanchor, Iso.refl_trans, Sigma.eta] using
    (node_associativity G D C L
    (a ≪≫ isoWhiskerLeft D.functor l) N M).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
local notation "D" => sourceReference P p
local notation "F" => pairReference P q w
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "C" => BassMWholeNerve.coefficientModel P (β.app b)
local notation "L" => CoefficientBassLaurentCompositionCarrier.reference P q w
local notation "G" => BassProjectionPath.WholeReference.reference P d (input P p q w)

/-- The entire lower row keeps the original sheet anchor and source chart before Laurent K. -/
def lowerProductAnchor : (G).functor ≅ ((D ≫ C) ≫ L).functor :=
  laurentAnchor P p q w β hd ≪≫ Functor.associator (D).functor (F).functor (J).functor ≪≫
    isoWhiskerLeft (D).functor (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w) ≪≫
    (Functor.associator (D).functor (C).functor (L).functor).symm

/-- Every full lower node, at every source-square node, has its exact Laurent-product form. -/
theorem lower_node (N : Node D) (M : Node L) :
    reanchor (laurentAnchor P p q w β hd)
      (node ((D ≫ F) ≫ J) D (F ≫ J)
        (Functor.associator (D).functor (F).functor (J).functor) N
        (reanchor (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w)
          (precompNode C M))) =
    node G (D ≫ C) L (lowerProductAnchor P p q w β hd) (postcompNode C N) M :=
  lower_product_node D F J C L G (laurentAnchor P p q w β hd)
    (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w) N M

/-- The original correction preserves its complete Laurent-side family at height zero. -/
theorem pair_lower (r : I) :
    CoefficientBassRaw1PolynomialPairCone.corrected P β q w (r, 0) =
      SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _))
        (mapParameter (fun M ↦ reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w) (precompNode C M))
          (CoefficientBassLaurentCompositionCarrier.family P q w r)) := by
  have h := (CoefficientBassRaw1PolynomialPairCone.correctedSquare P β q w).left r
  change CoefficientBassRaw1PolynomialPairCone.corrected P β q w (r, 0) =
    SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β q w (r, 0)) at h
  rw [CoefficientBassRaw1PolynomialLowerAttachment.sheetFamily_lower] at h
  exact h

/-- The source-square action at height zero retains the whole original lower Laurent parameter. -/
theorem family_lower (r t : I) : family P p q w β ((r, 0), t) =
    FiniteSourceSheet.targetLaurent D F J
      (FiniteSourceSheet.laurent D F J (CoefficientSquareFamilies.polynomialNodes P p)
        (mapParameter (fun M ↦ reanchor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β q w) (precompNode C M))
          (CoefficientBassLaurentCompositionCarrier.family P q w r),
          NativeSquareFiveSimplex.parameter t)) := by
  change FiniteSourceSheet.action D F J (CoefficientSquareFamilies.polynomialNodes P p)
    (CoefficientBassRaw1PolynomialPairCone.corrected P β q w (r, 0),
      NativeSquareFiveSimplex.parameter t) = _
  rw [pair_lower, FiniteSourceSheet.action_laurent]

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
