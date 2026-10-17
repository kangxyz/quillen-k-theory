/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialLowerAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence

/-! The actual lower-sheet anchor is the complete binary chart-naturality transport. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialLowerNormalization
open BassReferenceMerge

private theorem eq_chain {C D : Type u} [Category C] [Category D]
    {F G H K : C ⥤ D} (h₁ : F = G) (h₂ : G = H) (h₃ : F = H) (e : H ≅ K) :
    smallIso (eqToIso h₁) ≪≫ smallIso (eqToIso h₂ ≪≫ e) =
      smallIso (eqToIso h₃) ≪≫ smallIso e := by
  rw [← smallIso_trans, ← smallIso_trans, ← Iso.trans_assoc, eqToIso_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "Pp" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) p)
local notation "Pq" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) q)
local notation "Lp" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) p)
local notation "Lq" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) q)
local notation "ja" => coefficientMap P (β.app a)
local notation "jb" => coefficientMap P (β.app b)
local notation "jc" => coefficientMap P (β.app c)
local notation "N" => boundedFlatNormalizedPullback

/-- The source and target chart composites are related by the original naturality square. -/
theorem pair_naturality : jc ≫ (Pq ≫ Pp) = (Lq ≫ Lp) ≫ ja := by
  have h := coefficientMap_naturality P β (p ≫ q)
  simpa only [Functor.map_comp, coefficientMap_comp] using h.symm

/-- The last source transport and right-first association retain precisely this binary total. -/
theorem lower_transport :
    DoubleSquareCommonSimplex.lastSourceIso Pp Pq Lp Lq ja jb jc
      (coefficientMap_naturality P β p).symm (coefficientMap_naturality P β q).symm ≪≫
        NormalizedTripleSimplex.rightFirst Lq Lp ja =
      smallIso (eqToIso (congrArg N (pair_naturality P β p q))) ≪≫
        BinaryNormalizationSimplex.total (Lq ≫ Lp) ja := by
  exact eq_chain
    (congrArg N (((DoubleSquareTrack.total_eq Pp Pq Lp Lq ja jb jc
      (coefficientMap_naturality P β p).symm
      (coefficientMap_naturality P β q).symm).symm).trans (Category.assoc Lq Lp ja)))
    (congrArg N (Category.assoc Lq Lp ja).symm)
    (congrArg N (pair_naturality P β p q))
    (boundedFlatNormalizedPullbackCompIso (Lq ≫ Lp) ja)

/-- The original paused lower anchor equals the literal complete chart-naturality word. -/
theorem lowerAnchor_normalized :
    CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q =
      (BinaryNormalizationSimplex.total jc (Pq ≫ Pp)).symm ≪≫
        smallIso (eqToIso (congrArg N (pair_naturality P β p q))) ≪≫
          BinaryNormalizationSimplex.total (Lq ≫ Lp) ja := by
  unfold CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor
  rw [lower_transport]
  rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialLowerNormalization
