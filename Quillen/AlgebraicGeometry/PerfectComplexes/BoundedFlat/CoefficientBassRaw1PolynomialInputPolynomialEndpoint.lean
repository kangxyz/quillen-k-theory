/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputEndpointWord

/-! The complete polynomial endpoint shared by the radial and input caps. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputPolynomialEndpoint
open CommonReferenceNerve BassH0Merge

private theorem node_of_equality {V W : Model.{u}} (F H K : V ⟶ W)
    (e : H.functor = K.functor) (δ : F.functor ≅ H.functor) (η : F.functor ≅ K.functor)
    (h : δ ≪≫ eqToIso e = η) : (⟨H, δ⟩ : Node F) = ⟨K, η⟩ := by
  have he : H = K := Model.Hom.ext e
  subst K
  simp only [eqToIso_refl, Iso.trans_refl] at h
  subst η
  rfl

private theorem precomp_source {V W T : Model.{u}} (F : V ⟶ T) (A : V ⟶ W) (H : W ⟶ T)
    (δ : F.functor ≅ (A ≫ H).functor) :
    CommonReferenceProduct.reanchor δ (precompNode A (⟨H, Iso.refl _⟩ : Node H)) =
      (⟨A ≫ H, δ⟩ : Node F) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change δ ≪≫ isoWhiskerLeft A.functor (Iso.refl H.functor) = δ
  rw [isoWhiskerLeft_refl]
  exact Iso.trans_refl δ

private theorem left_eqToIso {C D E : Type u} [Category C] [Category D] [Category E]
    (A : C ⥤ D) (F G : D ⥤ E) (h : F = G) :
    isoWhiskerLeft A (eqToIso h) = eqToIso (congrArg (fun K ↦ A ⋙ K) h) := by
  subst G
  exact isoWhiskerLeft_refl A F

private theorem mapped_parameter_congr {V W X Y Z T : Model.{u}}
    (F : V ⟶ W) (G : X ⟶ W) (H : Y ⟶ Z) (K : X ⟶ T)
    (f : Node F → Node G) (g : Node G → Node K) (h : Node H → Node K)
    (N : Fin 1 → Node F) (M : Fin 1 → Node H) (z : StdSimplex ℝ (Fin 1))
    (e : ∀ i, g (f (N i)) = h (M i)) :
    mapParameter g (mapParameter f (parameter F N z)) = mapParameter h (parameter H M z) := by
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns ↦ parameter K ns z) (funext e)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The source-precomposed pair source node is the original radial pair target node. -/
theorem polynomial_node :
    CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w)
      (precompNode (CoefficientBassSeedTargetChartAttachment.M P p)
        (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map w))
          (coefficientMap P ((polynomialUnderFunctor R).map q)) 0)) =
    CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map (q ≫ w)))
        (coefficientMap P ((polynomialUnderFunctor R).map p)) 2) := by
  have hs := precomp_source (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
    (CoefficientBassSeedTargetChartAttachment.M P p)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
    (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w)
  refine hs.trans ?_
  have e := CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialEq P q w
  have hw := (CoefficientBassRaw1PolynomialInputEndpointWord.polynomial_word P p q w).symm
  have he := left_eqToIso (CoefficientBassSeedTargetChartAttachment.M P p).functor _ _ e
  dsimp only [CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso] at hw
  rw [he] at hw
  exact node_of_equality (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
    ((CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
    ((CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P (q ≫ w))
    (congrArg (fun F ↦ (CoefficientBassSeedTargetChartAttachment.M P p).functor ⋙ F) e)
    (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w) _ hw

/-- The original paused polynomial endpoints agree as whole nerve points. -/
theorem polynomial_parameter :
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w))
      (mapParameter (precompNode (CoefficientBassSeedTargetChartAttachment.M P p))
        (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 0)) =
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w))
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p (q ≫ w) 1) := by
  have h0 : CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 0 =
      parameter _ (fun _ : Fin 1 ↦ binaryNodes
        (coefficientMap P ((polynomialUnderFunctor R).map w))
        (coefficientMap P ((polynomialUnderFunctor R).map q)) 0) (StdSimplex.single 0) := by
    change parameter _ _ (CoefficientBassRaw1PolynomialSourceAttachment.pausedBinaryParameter 0) = _
    rw [Path.source]
    simpa only [StdSimplex.map_single, SimplexCategory.const_apply] using
      parameter_face (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
        (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map w))
          (coefficientMap P ((polynomialUnderFunctor R).map q)))
        (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) (StdSimplex.single 0)
  have h1 : CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p (q ≫ w) 1 =
      parameter _ (fun _ : Fin 1 ↦ binaryNodes
        (coefficientMap P ((polynomialUnderFunctor R).map (q ≫ w)))
        (coefficientMap P ((polynomialUnderFunctor R).map p)) 2) (StdSimplex.single 0) := by
    change parameter _ _ (CoefficientBassRaw1PolynomialSourceAttachment.pausedBinaryParameter 1) = _
    rw [Path.target]
    simpa only [StdSimplex.map_single, SimplexCategory.const_apply] using
      parameter_face (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w))
        (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map (q ≫ w)))
          (coefficientMap P ((polynomialUnderFunctor R).map p)))
        (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2) (StdSimplex.single 0)
  have hl := congrArg (fun y ↦ mapParameter (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w))
      (mapParameter (precompNode (CoefficientBassSeedTargetChartAttachment.M P p)) y)) h0
  have hr := congrArg (mapParameter (CommonReferenceProduct.reanchor
    (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w))) h1
  have hm := mapped_parameter_congr
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
    ((CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w))
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
    (precompNode (CoefficientBassSeedTargetChartAttachment.M P p))
    (CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w))
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w))
    (fun _ : Fin 1 ↦ binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((polynomialUnderFunctor R).map q)) 0)
    (fun _ : Fin 1 ↦ binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map (q ≫ w)))
      (coefficientMap P ((polynomialUnderFunctor R).map p)) 2)
    (StdSimplex.single 0) (fun _ ↦ polynomial_node P p q w)
  exact hl.trans (hm.trans hr.symm)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputPolynomialEndpoint
