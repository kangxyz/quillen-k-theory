/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatCochainResolution

/-! Semantic consumers of actual open-free flat resolutions and arbitrary pullback. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf
namespace QuillenTest.FlatSheafResolutions

open Quillen

/-- Each original local section is actually hit by its open-free generator. -/
theorem generator_hits_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) : openFreeHomEquiv X U M
      (Sigma.ι (fun t : localSectionIndex M => openFree X t.1)
        (⟨U, s⟩ : localSectionIndex M) ≫ flatCoverπ M) = s := by
  simp [flatCoverπ]

/-- The replacement theorem has no affineness, quasicoherence, or resolution premise. -/
theorem actual_flat_replacement (X : Scheme.{u}) (M : X.Modules) :
    ∃ (P : CochainComplex X.Modules ℤ)
      (p : P ⟶ (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M),
      (∀ n, stalkwiseFlat X (P.X n)) ∧ (∀ n, 0 < n → IsZero (P.X n)) ∧ QuasiIso p :=
  exists_boundedAbove_flat_resolution X M

/-- Actual comparison maps between constructed flat replacements survive arbitrary pullback. -/
theorem pullback_flat_resolution_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Y.Modules) (s : (flatCochainResolution Y).obj M ⟶ (flatCochainResolution Y).obj N)
    [QuasiIso s] : QuasiIso ((Quillen.PerfectComplexes.pullbackComplex f).map s) :=
  quasiIso_pullback_of_boundedAbove_stalkwiseFlat f
    (flatCochainResolution_term_flat Y M) (flatCochainResolution_term_flat Y N) 0 0
    (flatCochainResolution_isZero_above Y M) (flatCochainResolution_isZero_above Y N) s

/-- A flat original module needs no flatness assumption on the scheme morphism. -/
theorem pullback_flat_resolution_augmentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hM : stalkwiseFlat Y M) :
    QuasiIso ((Quillen.PerfectComplexes.pullbackComplex f).map (flatCochainResolutionπ Y M)) :=
  quasiIso_pullback_flatCochainResolutionπ f M hM

/-- The flat cover source stays flat under an arbitrary change of scheme. -/
theorem pullback_flat_cover_stalks {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    stalkwiseFlat X ((Scheme.Modules.pullback f).obj (flatCover M)) :=
  stalkwiseFlat_pullback f (flatCover_stalkwiseFlat M)

/-- Actual flat kernel sequences, rather than an ambient exactness hypothesis, pull back. -/
theorem pullback_kernel_sequence_flat_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (hM : stalkwiseFlat Y M) :
    ((ShortComplex.mk (kernel.ι (flatCoverπ M)) (flatCoverπ M)
      (kernel.condition _)).map (Scheme.Modules.pullback f)).ShortExact :=
  shortExact_pullback_of_stalkwiseFlat_quotient f
    { exact := (ShortComplex.mk _ _ (kernel.condition (flatCoverπ M))).exact_of_f_is_kernel
        (kernelIsKernel (flatCoverπ M))
      mono_f := inferInstance
      epi_g := inferInstance } hM

end QuillenTest.FlatSheafResolutions
