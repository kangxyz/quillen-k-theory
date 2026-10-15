/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenSheafSequence
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts

/-!
# Consumers of the actual signed two-open sheaf sequence

Inspect original units, original section restrictions, the signed difference,
unique kernel factorization, functoriality, and the actual Laurent chart cover
of the projective line over arbitrary, nonreduced, and zero base rings.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
  AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent
namespace QuillenTest.TwoOpenSheafSequence

open Quillen
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : IsPullback a b j k) (M : X.Modules)

/-- The augmentation consists of the original two adjunction units. -/
theorem original_augmentation :
    (sheafSequence a b j k h.w M).f =
      prod.lift ((Scheme.Modules.restrictAdjunction j).unit.app M)
        ((Scheme.Modules.restrictAdjunction k).unit.app M) := rfl

/-- The difference retains the literal plus-minus order and actual common-overlap comparison. -/
theorem original_signed_difference :
    (sheafSequence a b j k h.w M).g =
      prod.fst ≫ openLocalizationMap a j M -
        prod.snd ≫ openLocalizationMap b k M ≫ (openLocalizationCongr h.w.symm).hom.app M := rfl

/-- The first smaller-open component is the literal original section restriction. -/
theorem original_section_restriction (T : X.Opens) :
    (openLocalizationMap a j M).app T =
      M.presheaf.map (homOfLE (openLocalization_image_le a j T)).op :=
  openLocalizationMap_app a j M T

/-- The original short exact sequence gives a unique factor through its actual augmentation. -/
theorem original_kernel_factorization
    (hcover : ∀ x : X, (∃ y : U, j y = x) ∨ (∃ z : V, k z = x))
    (P : X.Modules) (q : P ⟶ (sheafSequence a b j k h.w M).X₂)
    (hq : q ≫ (sheafSequence a b j k h.w M).g = 0) :
    ∃! l : P ⟶ M, l ≫ (sheafSequence a b j k h.w M).f = q := by
  let S := sheafSequence a b j k h.w M
  have hS := sheafSequence_shortExact a b j k h M hcover
  let : Mono S.f := hS.mono_f
  let c := KernelFork.ofι q hq
  let l := hS.fIsKernel.lift c
  have hl : l ≫ S.f = q := Fork.IsLimit.lift_ι (t := c) hS.fIsKernel
  refine ⟨l, hl, ?_⟩
  intro m hm
  exact (cancel_mono S.f).mp (hm.trans hl.symm)

/-- Original sequence morphisms preserve composition on the nose. -/
theorem original_sequence_composition {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    sheafSequenceMap a b j k h.w (φ ≫ ψ) =
      sheafSequenceMap a b j k h.w φ ≫ sheafSequenceMap a b j k h.w ψ :=
  (sheafSequenceFunctor a b j k h.w).map_comp φ ψ

/-- The original quotient differential commutes with arbitrary coefficient morphisms. -/
theorem original_difference_naturality {M N : X.Modules} (φ : M ⟶ N) :
    prod.map ((openLocalization j).map φ) ((openLocalization k).map φ) ≫
      sheafDifference a b j k h.w N =
    sheafDifference a b j k h.w M ≫ (openLocalization (a ≫ j)).map φ :=
  (sheafSequenceMap a b j k h.w φ).comm₂₃

/-- The genuine Laurent intersection supplies the actual projective-line sheaf resolution. -/
theorem original_projective_sequence (R : CommRingCat.{u}) (M : (twoChartLine R).Modules) :
    (sheafSequence (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R)
      (overlap_equation R) M).ShortExact :=
  sheafSequence_shortExact _ _ _ _ (chart_isPullback R) M (charts_jointly_surjective R)

/-- The actual Laurent-chart resolution works over a nonreduced ring. -/
theorem nonreduced_sequence (M : (twoChartLine (CommRingCat.of (ZMod 4))).Modules) :
    (sheafSequence (laurentPlus (CommRingCat.of (ZMod 4)))
      (laurentMinus (CommRingCat.of (ZMod 4))) (plusChart (CommRingCat.of (ZMod 4)))
      (minusChart (CommRingCat.of (ZMod 4))) (overlap_equation (CommRingCat.of (ZMod 4)))
      M).ShortExact := original_projective_sequence _ M

/-- The zero-ring case retains the same original sequence and maps. -/
theorem zero_ring_sequence (M : (twoChartLine (CommRingCat.of (ZMod 1))).Modules) :
    (sheafSequence (laurentPlus (CommRingCat.of (ZMod 1)))
      (laurentMinus (CommRingCat.of (ZMod 1))) (plusChart (CommRingCat.of (ZMod 1)))
      (minusChart (CommRingCat.of (ZMod 1))) (overlap_equation (CommRingCat.of (ZMod 1)))
      M).ShortExact := original_projective_sequence _ M

end QuillenTest.TwoOpenSheafSequence
