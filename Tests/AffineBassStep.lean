/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStep
public import Mathlib.Data.ZMod.Basic

/-!
Consumers retain the original scalar action, geometric maps, all double-loop based edges, whole
two-time structure equation and original Laurent/nullhomotopy-conjugated transition.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.AffineBassStep
open Quillen.LoopPrespectrum Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
  Quillen.Scheme.PolynomialLaurent

/-- All four based edges and the full transpose involution retain the original point. -/
theorem transpose_edges {X : Type u} [TopologicalSpace X] (x : X)
    (γ : Path (Path.refl x) (Path.refl x)) (s : unitInterval) :
    doubleLoopTranspose x γ 0 s = x ∧ doubleLoopTranspose x γ 1 s = x ∧
      doubleLoopTranspose x γ s 0 = x ∧ doubleLoopTranspose x γ s 1 = x ∧
      doubleLoopTranspose x (doubleLoopTranspose x γ) = γ := by
  refine ⟨(γ s).source, (γ s).target, ?_, ?_, (doubleLoopTransposeHomeomorph x).left_inv γ⟩
  · change γ 0 s = x
    rw [γ.source]
    rfl
  · change γ 1 s = x
    rw [γ.target]
    rfl

/-- The structure coordinate is outside the loop coordinate, with no implicit sign transport. -/
theorem parameter_order (E : LoopPrespectrum.{u}) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) (s t : unitInterval) :
    Path.toContinuousMap ((parameterLooping E).structureMap n γ t) s = E.structureMap n (γ s) t :=
      rfl

/-- The original self-homotopy at zero supplies the whole actual loop. -/
theorem original_zero_track {E F : LoopPrespectrum.{u}}
    (H : Homotopy (Quillen.LoopPrespectrum.zeroHom E F) (Quillen.LoopPrespectrum.zeroHom E F)) (n :
      ℕ) (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap (H.zeroLoopMap.map n x) s = H.level n (s,x) := rfl

/-- Scalar multiplication is on the original section module, without a QC premise. -/
theorem original_section_action (X : Scheme.{u}) (r : Γ(X, ⊤)) (M : X.Modules)
    (U : X.Opens) (m : M.val.obj (op U)) :
    ((SchemeSheaf.globalScalar X r).app M).val.app (op U) m =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • m := rfl

/-- The original scalar and inverse scalar compose to the literal identity. -/
theorem original_unit_inverse (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (M : X.Modules) :
    (SchemeSheaf.globalUnitIso X r).hom.app M ≫ (SchemeSheaf.globalUnitIso X r).inv.app M = 𝟙 M ∧
      (SchemeSheaf.globalUnitIso X r).inv.app M ≫ (SchemeSheaf.globalUnitIso X r).hom.app M = 𝟙 M :=
  ⟨(SchemeSheaf.globalUnitIso X r).hom_inv_id_app M, (SchemeSheaf.globalUnitIso X r).inv_hom_id_app
    M⟩

/-- The literal chain action has the original module-sheaf scalar in every degree. -/
theorem original_chain_action (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (K : Complex X) (n : ℤ) :
    ((complexGlobalUnitIso X r).hom.app K).f n =
      (SchemeSheaf.globalUnitIso X r).hom.app (K.X n) := complexGlobalUnitIso_original_terms X r K n

/-- The chosen global unit is the actual Laurent coordinate under the original affine ring iso. -/
theorem original_T (R : CommRingCat.{u}) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom (↑(laurentGlobalUnit R)) = LaurentPolynomial.T
      1 :=
  laurentGlobalUnit_original_T R

/-- Both actual geometric polynomial triangles commute. -/
theorem original_scheme_triangles (R : CommRingCat.{u}) :
    laurentPlus R ≫ polynomialProjection R = laurentProjection R ∧
      laurentMinus R ≫ polynomialProjection R = laurentProjection R :=
  ⟨laurentPlus_projection R, laurentMinus_projection R⟩

/-- Both original legs of the genuine double-cylinder comparison are retained. -/
theorem original_square_legs (R : CommRingCat.{u}) :
    HomotopyPushout.inl (perfectFlatPrespectrumMap (polynomialProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R)) ≫ bassSquareComparison R =
      perfectFlatPrespectrumMap (laurentPlus R) ∧
    HomotopyPushout.inr (perfectFlatPrespectrumMap (polynomialProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R)) ≫ bassSquareComparison R =
      perfectFlatPrespectrumMap (laurentMinus R) :=
  ⟨HomotopyPushout.inl_desc _ _ _ _ _, HomotopyPushout.inr_desc _ _ _ _ _⟩

/-- The nullhomotopy retains both original prespectrum-map endpoints. -/
theorem original_null_endpoints (R : CommRingCat.{u}) :
    (bassLaurentNullHomotopy R).at 0 =
      perfectFlatPrespectrumMap (laurentProjection R) ≫ mappingConeInclusion (bassSquareComparison
        R) ∧
      (bassLaurentNullHomotopy R).at 1 = Quillen.LoopPrespectrum.zeroHom _ _ :=
  ⟨(bassLaurentNullHomotopy R).at_zero_eq, (bassLaurentNullHomotopy R).at_one_eq⟩

/-- The full two-time structure square is exact for the original affine transition. -/
theorem original_transition_square (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (perfectWaldhausen (Spec R))).space n) (s t : unitInterval) :
    Path.toContinuousMap ((affineBassTransition R).map (n+1)
      ((originalPrespectrum (perfectWaldhausen (Spec R))).structureMap n x t)) s =
    Path.toContinuousMap ((affineBassStep R).structureMap n ((affineBassTransition R).map n x) t) s
      :=
  congrArg (fun p ↦ Path.toContinuousMap (p t) s) ((affineBassTransition R).comm n x)

/--
The whole interior loop remains the original Laurent track conjugated by the displayed nullhomotopy.
-/
theorem original_transition_loop (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (perfectWaldhausen (Spec R))).space n) (s : unitInterval) :
    Path.toContinuousMap ((affineBassTransition R).map n x) s =
      (((laurentUnitHomotopy R).postcomp (mappingConeInclusion (bassSquareComparison
        R))).conjugateToZero
        (bassLaurentNullHomotopy R)).level n (s,x) := affineBassTransition_apply R n x s

/-- Empty spectrum does not introduce a nontrivial-ring hypothesis into the actual transition. -/
theorem empty_spectrum_transition (n : ℕ) :
    (affineBassTransition (CommRingCat.of (ZMod 1))).map n
      ((originalPrespectrum (perfectWaldhausen (Spec (.of (ZMod 1))))).point n) =
        (affineBassStep (.of (ZMod 1))).point n :=
  (affineBassTransition (.of (ZMod 1))).map_point n

lemma original_coordinate_unit (R : CommRingCat.{u}) :
    (laurentCoordinateUnit R : LaurentPolynomial R) = LaurentPolynomial.T 1 ∧
    (↑((laurentCoordinateUnit R)⁻¹) : LaurentPolynomial R) = LaurentPolynomial.T (-1) := ⟨rfl,rfl⟩

lemma original_chart_ranges (R : CommRingCat.{u}) :
    (laurentPlus R).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) ∧
    (laurentMinus R).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) :=
  ⟨laurentPlus_opensRange R,laurentMinus_opensRange R⟩


end Quillen.Tests.AffineBassStep
