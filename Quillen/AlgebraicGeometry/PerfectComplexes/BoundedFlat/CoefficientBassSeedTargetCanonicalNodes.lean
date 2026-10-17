/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetCanonicalAnchor
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Whole ordinary and shifted canonical target attachment squares before evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetCanonicalNodes
open CommonReferenceNerve CommonReferenceProduct
open CoefficientBassSeedTargetChartAttachment CoefficientBassSeedTargetCanonicalAnchor
open BassH0Merge LaurentUnitReferenceSpecialization

private theorem attachment_square {V W T : Model.{u}} (F F' : V ⟶ W)
    (J : W ⟶ T) (G G' : V ⟶ T) (σ : F'.functor ≅ F.functor)
    (τ : G'.functor ≅ G.functor) (ε : G.functor ≅ (F ≫ J).functor)
    (ε' : G'.functor ≅ (F' ≫ J).functor)
    (h : τ ≪≫ ε = ε' ≪≫ isoWhiskerRight σ J.functor) (N : Node F) :
    reanchor τ (attachPostcompNode F J G ε N) =
      attachPostcompNode F' J G' ε' (reanchor σ N) := by
  rcases N with ⟨K, ρ⟩
  change (⟨K ≫ J, τ ≪≫ (ε ≪≫ isoWhiskerRight ρ J.functor)⟩ : Node G') =
    ⟨K ≫ J, ε' ≪≫ isoWhiskerRight (σ ≪≫ ρ) J.functor⟩
  apply congrArg (fun η : G'.functor ≅ (K ≫ J).functor ↦ (⟨K ≫ J, η⟩ : Node G'))
  calc
    τ ≪≫ (ε ≪≫ isoWhiskerRight ρ J.functor) =
        (τ ≪≫ ε) ≪≫ isoWhiskerRight ρ J.functor := (Iso.trans_assoc _ _ _).symm
    _ = (ε' ≪≫ isoWhiskerRight σ J.functor) ≪≫
        isoWhiskerRight ρ J.functor := congrArg (fun e ↦ e ≪≫ _) h
    _ = ε' ≪≫ isoWhiskerRight (σ ≪≫ ρ) J.functor := by
      simp only [isoWhiskerRight_trans, Iso.trans_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {X : Scheme.{u}} (h : space (op P, (polynomialUnderFunctor R).obj a) ⟶ X)
local notation "l" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "m" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) f)
local notation "ja" => laurentPlus P a

/-- Every ordinary target-sheet node has its prescribed canonical full anchor. -/
theorem ordinary_node (N : Node (normalizedMap h ≫ M P f)) :
    reanchor (BinaryNormalizationSimplex.total l (ja ≫ h))
      (attachPostcompNode (normalizedMap h ≫ M P f) (Jb P (b := b))
        (normalizedMap (ja ≫ h) ≫ L P f)
        (targetAnchor P f (normalizedMap h) (normalizedMap (ja ≫ h))
          (BinaryNormalizationSimplex.total ja h)) N) =
    attachPostcompNode (normalizedMap (m ≫ h)) (Jb P (b := b))
      (normalizedMap (l ≫ ja ≫ h)) (canonicalAnchor P f h)
      (reanchor (BinaryNormalizationSimplex.total m h) N) :=
  attachment_square _ _ _ _ _ _ _ _ _ (ordinary_model_anchor P f h) N

/-- Every shifted target-sheet node retains the exact target inner-unit action. -/
theorem shifted_node (N : Node (normalizedMap h ≫ M P f)) :
    reanchor (BinaryNormalizationSimplex.total l (ja ≫ h))
      (attachPostcompNode (normalizedMap h ≫ M P f) (Jb P (b := b))
        (normalizedMap (ja ≫ h) ≫ L P f)
        (targetAnchor P f (normalizedMap h) (normalizedMap (ja ≫ h))
          (onFunctor (normalizedMap (ja ≫ h)).functor (smallUnit P a) ≪≫
            BinaryNormalizationSimplex.total ja h)) N) =
    attachPostcompNode (normalizedMap (m ≫ h)) (Jb P (b := b))
      (normalizedMap (l ≫ ja ≫ h))
      (onFunctor (normalizedMap (l ≫ ja ≫ h)).functor (smallUnit P b) ≪≫
        canonicalAnchor P f h)
      (reanchor (BinaryNormalizationSimplex.total m h) N) := by
  apply attachment_square
  exact (shifted_model_anchor P f h).trans (Iso.trans_assoc _ _ _).symm

/-- The ordinary canonical attachment square holds on the entire nerve realization. -/
theorem ordinary_parameter
    (y : |nerve (Codiscrete (Node (normalizedMap h ≫ M P f)))|) :
    mapParameter (reanchor (BinaryNormalizationSimplex.total l (ja ≫ h)))
      (mapParameter
        (attachPostcompNode (normalizedMap h ≫ M P f) (Jb P (b := b))
          (normalizedMap (ja ≫ h) ≫ L P f)
          (targetAnchor P f (normalizedMap h) (normalizedMap (ja ≫ h))
            (BinaryNormalizationSimplex.total ja h))) y) =
    mapParameter
      (attachPostcompNode (normalizedMap (m ≫ h)) (Jb P (b := b))
        (normalizedMap (l ≫ ja ≫ h)) (canonicalAnchor P f h))
      (mapParameter (reanchor (BinaryNormalizationSimplex.total m h)) y) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter (normalizedMap h ≫ M P f) y
  rw [← hz]
  erw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin (k + 1) → Node (normalizedMap (l ≫ ja ≫ h)) ↦
    parameter (normalizedMap (l ≫ ja ≫ h)) ns z)
      (funext fun i ↦ ordinary_node P f h (N i))

/-- The whole shifted attachment square keeps the target unit at every nerve point. -/
theorem shifted_parameter
    (y : |nerve (Codiscrete (Node (normalizedMap h ≫ M P f)))|) :
    mapParameter (reanchor (BinaryNormalizationSimplex.total l (ja ≫ h)))
      (mapParameter
        (attachPostcompNode (normalizedMap h ≫ M P f) (Jb P (b := b))
          (normalizedMap (ja ≫ h) ≫ L P f)
          (targetAnchor P f (normalizedMap h) (normalizedMap (ja ≫ h))
            (onFunctor (normalizedMap (ja ≫ h)).functor (smallUnit P a) ≪≫
              BinaryNormalizationSimplex.total ja h))) y) =
    mapParameter
      (attachPostcompNode (normalizedMap (m ≫ h)) (Jb P (b := b))
        (normalizedMap (l ≫ ja ≫ h))
        (onFunctor (normalizedMap (l ≫ ja ≫ h)).functor (smallUnit P b) ≪≫
          canonicalAnchor P f h))
      (mapParameter (reanchor (BinaryNormalizationSimplex.total m h)) y) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter (normalizedMap h ≫ M P f) y
  rw [← hz]
  erw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin (k + 1) → Node (normalizedMap (l ≫ ja ≫ h)) ↦
    parameter (normalizedMap (l ≫ ja ≫ h)) ns z)
      (funext fun i ↦ shifted_node P f h (N i))

end Quillen.PerfectComplexes.CoefficientBassSeedTargetCanonicalNodes
