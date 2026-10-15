/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectComplement

/-! # Original perfect-target, empty-open and projection consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace QuillenTest.PerfectComplement
open Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Arbitrary original perfect terms give unique maps to every sufficiently low
quasicoherent single; no strict original source is required. -/
theorem original_perfect_low_single_subsingleton {X : Scheme.{u}} [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (E : Complex X) (hE : locallyPerfect X E) :
    ∃ c : ℤ, ∀ (M : X.Modules) [M.IsQuasicoherent], ∀ a : ℤ, a ≤ c →
      Subsingleton ((toDerived X).obj E ⟶
        (toDerived X).obj ((CochainComplex.singleFunctor X.Modules a).obj M)) := by
  obtain ⟨c, hc⟩ := locallyPerfect_exists_uniform_low_single_vanishing E hE
  exact ⟨c, fun M _ a ha => ⟨fun φ ψ => (hc M a ha φ).trans (hc M a ha ψ).symm⟩⟩

/-- Even an arbitrary all-sheaf complex on the empty open has an actual global
strict retract; no nonempty ring or cover premise is added. -/
theorem empty_open_original_global_strict_retract (R : CommRingCat.{u})
    (E : Complex (⊥ : (Spec R).Opens).toScheme) :
    ∃ Q : Complex (Spec R), strictPerfect (Spec R) Q ∧
      Nonempty (Retract ((toDerived (⊥ : (Spec R).Opens).toScheme).obj E)
        ((toDerived (⊥ : (Spec R).Opens).toScheme).obj ((restrict (⊥ : (Spec R).Opens).ι).obj Q)))
          := by
  apply locallyPerfect_exists_global_strict_retract R ⊥ (by simp) E
  intro x
  exact False.elim x.property

/-- The section is a section of the literal original f after associated sheaves,
restriction and the original derived target identification. -/
theorem original_projection_section (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
      :
    ∃ (K P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E)
      (σ : (toDerived W.toScheme).obj E ⟶
        (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P))),
      σ ≫ (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map f)) ≫ eK.hom = 𝟙
        _ := by
  obtain ⟨K, P, hP, f, eK, _, σ, hσ⟩ :=
    locallyPerfect_exists_original_strict_derived_retract R W hW E hE
  exact ⟨K, P, hP, f, eK, σ, hσ⟩

/-- The original approximation projection detects every outgoing derived map. -/
theorem original_projection_precomposition_injective (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
      :
    ∃ (K P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E),
      ∀ L : Derived W.toScheme, Function.Injective (fun φ : (toDerived W.toScheme).obj E ⟶ L =>
        originalApproximationHom R W.ι f eK ≫ φ) := by
  obtain ⟨K, P, hP, f, eK, _, σ, hσ⟩ :=
    locallyPerfect_exists_original_strict_derived_retract R W hW E hE
  refine ⟨K, P, hP, f, eK, fun L φ ψ h => ?_⟩
  have hh := congrArg (fun z => σ ≫ z) h
  simpa only [← Category.assoc, hσ, Category.id_comp] using hh

/-- The explicit actual complex complement is strict, the ambient model is
strict, and the inverse derived isomorphism preserves the actual chain projection. -/
theorem actual_complement_inverse_projection (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
      :
    ∃ (K P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K)
      (eK : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E) (C : Complex W.toScheme),
      strictPerfect W.toScheme C ∧
      ∃ e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
          (toDerived W.toScheme).obj (C ⊞ E),
        e.inv ≫ originalApproximationHom R W.ι f eK =
          (toDerived W.toScheme).map (biprod.snd : C ⊞ E ⟶ E) := by
  obtain ⟨K, P, n, hP, f, eK, _, _, hC, _, e, he⟩ :=
    locallyPerfect_exists_actual_perfect_complement R W hW E hE 0
  refine ⟨K, P, hP, f, eK, _, hC, e, ?_⟩
  rw [he, Iso.inv_hom_id_assoc]

/-- The actual vector-bundle complement is concentrated in term degree n+1,
recording the sign of the genuine inverse rotation. -/
theorem original_complement_term_degree (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E)
    (cutoff : ℤ) :
    ∃ (K P : ModuleComplex R) (n : ℤ) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      n ≤ cutoff ∧
      let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
      let C := ((CochainComplex.singleFunctor W.toScheme.Modules n).obj (D.homology n))⟦(-1 : ℤ)⟧
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree W.toScheme (D.homology n) ∧
        ∀ i : ℤ, i ≠ n+1 → IsZero (C.X i) := by
  obtain ⟨K, P, n, hP, f, _, hn, hM, _, _, _, _⟩ :=
    locallyPerfect_exists_actual_perfect_complement R W hW E hE cutoff
  refine ⟨K, P, n, hP, f, hn, hM, ?_⟩
  intro i hi
  let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
  let S := (CochainComplex.singleFunctor W.toScheme.Modules n).obj (D.homology n)
  exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n (D.homology n) (i + -1) (by omega)).of_iso
    (S.shiftFunctorObjXIso (-1) i (i + -1) rfl)

end QuillenTest.PerfectComplement
