/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows

/-! Exact normalization anchor of the second original composite chart row. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeReferenceAnchor
open BassH0Merge BassH1Join CoefficientMovingSquareRows
private theorem cancel_terminal {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ C) (J : C ⥤ D) (F : A ⥤ C) (S : A ⥤ D) (H : B ⥤ D)
    (η : F ≅ P ⋙ Q) (σ : S ≅ F ⋙ J) (ρ : S ≅ P ⋙ H) (κ : H ≅ Q ⋙ J)
    (h : σ ≪≫ isoWhiskerRight η J = ρ ≪≫ isoWhiskerLeft P κ) :
    isoWhiskerRight η J ≪≫ Functor.associator P Q J ≪≫ isoWhiskerLeft P κ.symm =
      σ.symm ≪≫ ρ := by
  have hc := congrArg (fun ν ↦ σ.symm ≪≫ ν ≪≫ (isoWhiskerLeft P κ).symm) h
  have ha : Functor.associator P Q J = Iso.refl _ := rfl
  simp only [ha, Iso.refl_trans]
  have hc' : isoWhiskerRight η J ≪≫ (isoWhiskerLeft P κ).symm = σ.symm ≪≫ ρ := by
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
      Iso.trans_refl] using hc
  simpa only [isoWhiskerLeft_symm] using hc'

variable {A B C B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (q' : C' ⟶ B')
  (b : B' ⟶ B) (c : C' ⟶ C) (hq : c ≫ q = q' ≫ b)

/-- The shared full reference node fixes both original terminal normalization words. -/
theorem terminal_anchor :
    BinaryNormalizationSimplex.total c (q ≫ p) ≪≫
      isoWhiskerRight (BinaryNormalizationSimplex.total q p) (normalizedMap c).functor =
    secondAnchor p q q' b c hq ≪≫
      isoWhiskerLeft (normalizedMap p).functor
        (NativeSquareFiveSimplex.sourceIso q' b c q hq.symm ≪≫
          BinaryNormalizationSimplex.total c q) := by
  have hs := source_side_nodes p q b q' p b c rfl hq 2
  have ht := second_row_nodes p q b q' p b c rfl hq 4
  have hn := hs.symm.trans ht
  exact eq_of_heq (Sigma.mk.inj hn).2

/-- The whole second row has the actual binary-polynomial sheet anchor. -/
theorem second_anchor :
    isoWhiskerRight (BinaryNormalizationSimplex.total q p) (normalizedMap c).functor ≪≫
      Functor.associator (normalizedMap p).functor (normalizedMap q).functor
        (normalizedMap c).functor ≪≫
      isoWhiskerLeft (normalizedMap p).functor
        (NativeSquareFiveSimplex.sourceIso q' b c q hq.symm ≪≫
          BinaryNormalizationSimplex.total c q).symm =
    (BinaryNormalizationSimplex.total c (q ≫ p)).symm ≪≫
      secondAnchor p q q' b c hq := by
  exact cancel_terminal (normalizedMap p).functor (normalizedMap q).functor
    (normalizedMap c).functor (BinaryNormalizationSimplex.sourceMap q p).functor
    (reference p q c).functor (NativeSquareFiveSimplex.source q' b).functor
    (BinaryNormalizationSimplex.total q p) (BinaryNormalizationSimplex.total c (q ≫ p))
    (secondAnchor p q q' b c hq)
    (NativeSquareFiveSimplex.sourceIso q' b c q hq.symm ≪≫ BinaryNormalizationSimplex.total c q)
    (terminal_anchor p q q' b c hq)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeReferenceAnchor
