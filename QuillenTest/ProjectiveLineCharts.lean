/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.GlobalSections
public import Mathlib.Data.ZMod.Basic

/-! Original-map consumers for the genuine two-chart scheme, including its
actual Laurent overlap, flat projection, qcqs source, exact global-section
isomorphism and coefficient inverse, and the zero-ring boundary. -/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Scheme.PolynomialLaurent Quillen.Scheme.ProjectiveLine
universe u
namespace QuillenTest.ProjectiveLineCharts

open Quillen

lemma original_overlap (R : CommRingCat.{u}) :
    IsPushout (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R) ∧
      IsPullback (laurentPlus R) (laurentMinus R) (plusChart R) (minusChart R) :=
  ⟨IsPushout.of_hasPushout _ _, chart_isPullback R⟩

lemma actual_chart_images (R : CommRingCat.{u}) :
    (plusChart R).opensRange ⊔ (minusChart R).opensRange = ⊤ ∧
      (plusChart R).opensRange ⊓ (minusChart R).opensRange =
        (laurentPlus R ≫ plusChart R).opensRange :=
  ⟨chart_ranges_cover R, chart_ranges_inter R⟩

lemma original_projection_is_flat (R : CommRingCat.{u}) :
    Flat (projection R) ∧ CompactSpace (twoChartLine R) ∧
      QuasiSeparatedSpace (twoChartLine R) := ⟨inferInstance,inferInstance,inferInstance⟩

lemma original_projection_sections (R : CommRingCat.{u}) :
    (globalSectionsIso R).hom =
      (Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (projection R).op ∧
    (globalSectionsIso R).inv = plusSections R ≫ CommRingCat.ofHom Polynomial.constantCoeff :=
  ⟨globalSectionsIso_hom R, globalSectionsIso_inv R⟩

lemma original_section_unique (R : CommRingCat.{u})
    (x : Γ(twoChartLine R, ⊤)) (r : R)
    (h : plusSections R x = Polynomial.C r) : baseSections R r = x := by
  have he := congrArg (fun f => f x) (globalSectionsIso_inv R)
  have hi : (globalSectionsIso R).inv x = r := by simpa [h] using he
  have hh := congrArg (fun f => f x) (globalSectionsIso R).inv_hom_id
  rw [globalSectionsIso_hom] at hh
  change baseSections R ((globalSectionsIso R).inv x) = x at hh
  rwa [hi] at hh

lemma empty_base_original_inverse :
    baseSections (.of (ZMod 1)) ≫ (globalSectionsIso (.of (ZMod 1))).inv = 𝟙 _ := by
  rw [← globalSectionsIso_hom]
  exact Iso.hom_inv_id _

end QuillenTest.ProjectiveLineCharts
