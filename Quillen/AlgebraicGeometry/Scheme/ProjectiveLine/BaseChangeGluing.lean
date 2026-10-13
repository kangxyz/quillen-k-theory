/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.BaseChange
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-! # Cartesian coefficient change for the original projective line

The original coefficient squares form an equifibered gluing diagram. Relative gluing identifies
its actual chart inverse images, retaining the original two-chart scheme and its structural map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialBaseChange

private abbrev chartCover (R : CommRingCat.{u}) :=
  AlgebraicGeometry.Scheme.IsLocallyDirected.openCover (span (laurentPlus R) (laurentMinus R))

private abbrev chartCoverCategory (R : CommRingCat.{u}) : Category (chartCover R).I₀ :=
  inferInstanceAs (Category WalkingSpan)

attribute [local instance] chartCoverCategory

private instance chartCoverThin (R : CommRingCat.{u}) : Quiver.IsThin (chartCover R).I₀ :=
  inferInstanceAs (Quiver.IsThin WalkingSpan)

private instance chartCoverLocallyDirected (R : CommRingCat.{u}) :
    (chartCover R).LocallyDirected where
  trans {i j} h := (span (laurentPlus R) (laurentMinus R)).map h
  w {i j} h := colimit.w (span (laurentPlus R) (laurentMinus R)) h
  directed {i j} x := by
    have he : colimit.ι (span (laurentPlus R) (laurentMinus R)) i
        (pullback.fst ((chartCover R).f i) ((chartCover R).f j) x) =
      colimit.ι (span (laurentPlus R) (laurentMinus R)) j
        (pullback.snd ((chartCover R).f i) ((chartCover R).f j) x) :=
      congrArg (fun k : pullback ((chartCover R).f i) ((chartCover R).f j) ⟶ twoChartLine R => k x)
        pullback.condition
    obtain ⟨k, ki, kj, y, hi, hj⟩ :=
      (AlgebraicGeometry.Scheme.IsLocallyDirected.ι_eq_ι_iff
        (span (laurentPlus R) (laurentMinus R))).mp he
    refine ⟨k, ki, kj, y, ?_⟩
    apply (pullback.fst ((chartCover R).f i) ((chartCover R).f j)).injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hi
  property_trans {i j} h := by cases h <;> infer_instance

private def coefficientDiagram {R S : CommRingCat.{u}} (f : R ⟶ S) :
    span (laurentPlus S) (laurentMinus S) ⟶ (chartCover R).functorOfLocallyDirected where
  app i := match i with
    | .none => Spec.map (laurentMap f)
    | .some .left => Spec.map (polynomialMap f)
    | .some .right => Spec.map (polynomialMap f)
  naturality i j h := by
    cases h with
    | id => change (𝟙 _) ≫ _ = _ ≫ (𝟙 _); simp only [Category.id_comp, Category.comp_id]
    | init j =>
      cases j with
      | left => exact (laurentMap_plus f).symm
      | right => exact (laurentMap_minus f).symm

private def coefficientGluing {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (chartCover R).RelativeGluingData where
  functor := span (laurentPlus S) (laurentMinus S)
  natTrans := coefficientDiagram f
  equifibered := by
    intro i j h
    cases h with
    | id => exact IsPullback.of_id_fst
    | init j =>
      cases j with
      | left => exact laurentPlus_isPullback f
      | right => exact laurentMinus_isPullback f

private lemma coefficientGluing_toBase {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (coefficientGluing f).toBase = coefficientMap f := by
  apply pushout.hom_ext
  · exact ((coefficientGluing f).ι_toBase WalkingSpan.left).trans
      (plusChart_coefficientMap f).symm
  · exact ((coefficientGluing f).ι_toBase WalkingSpan.right).trans
      (minusChart_coefficientMap f).symm

/-- The original positive chart is the actual inverse image under coefficient change. -/
lemma plusChart_coefficientMap_isPullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPullback (Spec.map (polynomialMap f)) (plusChart S) (plusChart R) (coefficientMap f) := by
  have h := (coefficientGluing f).isPullback_natTrans_ι_toBase WalkingSpan.left
  change IsPullback (Spec.map (polynomialMap f)) (plusChart S) (plusChart R)
    (coefficientGluing f).toBase at h
  rwa [coefficientGluing_toBase] at h

/-- The original negative chart is the actual inverse image under coefficient change. -/
lemma minusChart_coefficientMap_isPullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPullback (Spec.map (polynomialMap f)) (minusChart S) (minusChart R) (coefficientMap f) := by
  have h := (coefficientGluing f).isPullback_natTrans_ι_toBase WalkingSpan.right
  change IsPullback (Spec.map (polynomialMap f)) (minusChart S) (minusChart R)
    (coefficientGluing f).toBase at h
  rwa [coefficientGluing_toBase] at h

/-- Coefficient change of the original two-chart projective line is actual base change of
its original structural projection, for every commutative-ring map. -/
lemma coefficientMap_isPullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPullback (coefficientMap f) (projection S) (projection R) (Spec.map f) := by
  apply AlgebraicGeometry.Scheme.isPullback_of_openCover _ _ _ _ (chartCover R)
  intro i
  have hc := (coefficientGluing f).isPullback_natTrans_ι_toBase i
  rw [coefficientGluing_toBase] at hc
  have hp : IsPullback ((coefficientDiagram f).app i)
      (colimit.ι (span (laurentPlus S) (laurentMinus S)) i ≫ projection S)
      ((chartCover R).f i ≫ projection R) (Spec.map f) := by
    cases i with
    | none =>
      change IsPullback (Spec.map (laurentMap f))
        (colimit.ι (span (laurentPlus S) (laurentMinus S)) WalkingSpan.zero ≫ projection S)
        (colimit.ι (span (laurentPlus R) (laurentMinus R)) WalkingSpan.zero ≫ projection R)
        (Spec.map f)
      rw [← colimit.w (span (laurentPlus S) (laurentMinus S)) WalkingSpan.Hom.fst,
        ← colimit.w (span (laurentPlus R) (laurentMinus R)) WalkingSpan.Hom.fst]
      change IsPullback (Spec.map (laurentMap f))
        ((laurentPlus S ≫ plusChart S) ≫ projection S)
        ((laurentPlus R ≫ plusChart R) ≫ projection R) (Spec.map f)
      simpa only [Category.assoc, plusChart_projection, laurentPlus_projection] using
        (laurentProjection_isPullback f).flip
    | some i =>
      cases i with
      | left =>
        change IsPullback (Spec.map (polynomialMap f)) (plusChart S ≫ projection S)
          (plusChart R ≫ projection R) (Spec.map f)
        simpa only [plusChart_projection] using (polynomialProjection_isPullback f).flip
      | right =>
        change IsPullback (Spec.map (polynomialMap f)) (minusChart S ≫ projection S)
          (minusChart R ≫ projection R) (Spec.map f)
        simpa only [minusChart_projection] using (polynomialProjection_isPullback f).flip
  exact hp.of_iso hc.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [AlgebraicGeometry.Scheme.Cover.pullbackHom]; rfl)
    (by simp; rfl) (by simp) (by simp)

end Quillen.Scheme.ProjectiveLine
