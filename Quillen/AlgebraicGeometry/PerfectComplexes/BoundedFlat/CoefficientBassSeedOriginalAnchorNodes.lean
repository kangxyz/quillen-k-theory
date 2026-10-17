/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedOriginalAnchorNormalization
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Whole-node and whole-parameter normalization of the unchanged original chart sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedOriginalAnchorNodes
open BassH0Merge CommonReferenceNerve CommonReferenceProduct
open CoefficientBassSeedOriginalAnchorNormalization
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (p : a ⟶ b) (q : b ⟶ c)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
local notation "j" => coefficientMap P (α.app c)
local notation "g" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) q) ≫
  coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) p)
local notation "h" => polynomialProjection P a
local notation "D" => BassOverlap.projectionMap P (a := a) ≫ BassMOuterJoin.sideBinarySource P p q
local notation "G" => BassOverlap.commonReference P p q

/-- Each original sheet node retains its complete anchor after polynomial normalization. -/
theorem ordinary_node (N : Node D) :
    attachPostcompNode D (normalizedMap j) G (BassMOuterJoin.oldSideIso P p q α hc) N =
      attachPostcompNode (normalizedMap (g ≫ h)) (normalizedMap j) G
        (normalizedAnchor P p q α hc) (reanchor (BinaryNormalizationSimplex.total g h) N) := by
  rcases N with ⟨K, ρ⟩
  change (⟨K ≫ normalizedMap j, BassMOuterJoin.oldSideIso P p q α hc ≪≫
      isoWhiskerRight ρ (normalizedMap j).functor⟩ : Node G) =
    ⟨K ≫ normalizedMap j, normalizedAnchor P p q α hc ≪≫
      isoWhiskerRight (BinaryNormalizationSimplex.total g h ≪≫ ρ)
        (normalizedMap j).functor⟩
  apply congrArg (fun η : (G).functor ≅ (K ≫ normalizedMap j).functor ↦
    (⟨K ≫ _, η⟩ : Node G))
  rw [old_side_normalized, isoWhiskerRight_trans, Iso.trans_assoc]

/-- The same whole-node normalization preserves the original common-unit shifted sheet. -/
theorem shifted_node (N : Node D) :
    attachPostcompNode D (normalizedMap j) G
      (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫
        BassMOuterJoin.oldSideIso P p q α hc) N =
      attachPostcompNode (normalizedMap (g ≫ h)) (normalizedMap j) G
        (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ normalizedAnchor P p q α hc)
        (reanchor (BinaryNormalizationSimplex.total g h) N) := by
  rw [← reanchor_attach_node, ordinary_node, reanchor_attach_node]

/-- The entire original ordinary attachment agrees with its normalized parameter map. -/
theorem ordinary_parameter (y : |nerve (Codiscrete (Node D))|) :
    mapParameter (attachPostcompNode D (normalizedMap j) G
      (BassMOuterJoin.oldSideIso P p q α hc)) y =
      mapParameter (attachPostcompNode (normalizedMap (g ≫ h)) (normalizedMap j) G
        (normalizedAnchor P p q α hc))
        (mapParameter (reanchor (BinaryNormalizationSimplex.total g h)) y) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter D y
  rw [← hz]
  erw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin (k + 1) → Node G ↦ parameter G ns z)
    (funext fun i ↦ ordinary_node P p q α hc (N i))

/-- The entire shifted parameter square keeps its literal original common-unit action. -/
theorem shifted_parameter (y : |nerve (Codiscrete (Node D))|) :
    mapParameter (attachPostcompNode D (normalizedMap j) G
      (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫
        BassMOuterJoin.oldSideIso P p q α hc)) y =
      mapParameter (attachPostcompNode (normalizedMap (g ≫ h)) (normalizedMap j) G
        (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫ normalizedAnchor P p q α hc))
        (mapParameter (reanchor (BinaryNormalizationSimplex.total g h)) y) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter D y
  rw [← hz]
  erw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin (k + 1) → Node G ↦ parameter G ns z)
    (funext fun i ↦ shifted_node P p q α hc (N i))

end Quillen.PerfectComplexes.CoefficientBassSeedOriginalAnchorNodes
