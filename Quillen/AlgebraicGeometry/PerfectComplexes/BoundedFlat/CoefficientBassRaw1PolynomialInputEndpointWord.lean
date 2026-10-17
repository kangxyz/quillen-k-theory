/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialDirectSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputPlacement

/-! The original right-first polynomial word at the input cap endpoint. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputEndpointWord
open BassReferenceMerge BassH0Merge

private theorem rightFirst_eq {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.rightFirst f g h =
      eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) (Category.assoc f g h).symm) ≪≫
        BinaryNormalizationSimplex.total (f ≫ g) h := by
  have ht := smallIso_trans
    (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm))
    (boundedFlatNormalizedPullbackCompIso (f ≫ g) h)
  rw [smallIso_eqToIso] at ht
  exact ht

private theorem right_total_congr {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (k : X ⟶ Z) (e : f ≫ g = k) :
    eqToIso (congrArg (fun z ↦ (normalizedMap z).functor)
      ((Category.assoc f g h).symm.trans (congrArg (fun z ↦ z ≫ h) e))) ≪≫
        BinaryNormalizationSimplex.total k h =
      NormalizedTripleSimplex.rightFirst f g h ≪≫
        isoWhiskerLeft (normalizedMap h).functor
          (eqToIso (congrArg (fun z ↦ (normalizedMap z).functor) e)) := by
  subst k
  simp only [eqToIso_refl, isoWhiskerLeft_refl]
  exact (rightFirst_eq f g h).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The actual input and radial references agree on the full polynomial cylinder endpoint. -/
theorem polynomial_word :
    CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w ≪≫
      BinaryNormalizationSimplex.total
        (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P (q ≫ w))
        (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P p) =
    CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w ≪≫
      isoWhiskerLeft (CoefficientBassSeedTargetChartAttachment.M P p).functor
        (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso P q w) := by
  have e : CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P w ≫
      CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P q =
        CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P (q ≫ w) := by
    simp only [CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow,
      CategoryTheory.Functor.map_comp, coefficientMap_comp]
  exact right_total_congr
    (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P w)
    (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P q)
    (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P p)
    (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P (q ≫ w)) e

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputEndpointWord
