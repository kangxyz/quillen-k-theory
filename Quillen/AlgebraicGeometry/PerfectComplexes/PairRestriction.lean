/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Restriction


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairPullback

/-!
# Original restriction naturality for arbitrary open-pair squares

The actual bounded-flat relative restriction maps commute without geometric
extra assumptions. The original relative-open restriction and ordinary perfect
restriction then commute with arbitrary pair pullback when both ambient schemes
and both opens are qc, retaining precisely their existing public K-maps.
This proves the endpoint square, not connecting-map naturality or TT density.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

theorem boundedFlatPerfectOpenRestriction_exact :
    Waldhausen.IsExact (boundedFlatPerfectOpenWaldhausen j).cof
      (boundedFlatPerfectOpenWaldhausen j).weq
      (boundedFlatPerfectWaldhausen U).cof (boundedFlatPerfectWaldhausen U).weq
      (boundedFlatPerfectPullback j) where
  zero := (boundedFlatPerfectPullback_exact j).zero
  cofibration := (boundedFlatPerfectPullback_exact j).cofibration
  pushout := (boundedFlatPerfectPullback_exact j).pushout
  weak {K L} p hp := by
    let : QuasiIso ((restrict j).map p.hom) := hp
    let e := restrictIsoPullbackComplex j
    change QuasiIso ((AlgebraicGeometry.Scheme.Modules.Complex.pullback j).map p.hom)
    exact quasiIso_of_arrow_mk_iso ((restrict j).map p.hom)
      ((AlgebraicGeometry.Scheme.Modules.Complex.pullback j).map p.hom)
      (Arrow.isoMk (e.app K.obj) (e.app L.obj) (e.hom.naturality p.hom).symm)

/-- The degree-`n` K-map from the bounded-flat relative-open model for `j : U ⟶ X` to bounded-flat
perfect K-theory on `U`, induced by restriction. -/
def boundedFlatPerfectOpenKRestrict (n : ℕ) :
    BoundedFlatPerfectOpenK j n →* BoundedFlatPerfectK U n :=
  Waldhausen.KMap (boundedFlatPerfectOpenRestriction_exact j) n

theorem boundedFlatPerfectOpenKRestrict_comparison (n : ℕ) :
    (perfectOpenKRestrict j n).comp (boundedFlatPerfectOpenToPerfectOpenKMap j n) =
      (boundedFlatPerfectToPerfectKMap U n).comp (boundedFlatPerfectOpenKRestrict j n) := by
  unfold perfectOpenKRestrict boundedFlatPerfectOpenToPerfectOpenKMap
    boundedFlatPerfectToPerfectKMap boundedFlatPerfectOpenKRestrict
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedFlatPerfectOriginalRestrictionIso j) n

variable {A B : AlgebraicGeometry.Scheme.OpenPairs.{u}}

theorem boundedFlatPerfectOpenKRestrict_pullback (f : A ⟶ B) (n : ℕ) :
    (boundedFlatPerfectKPullback f.hom.left n).comp (boundedFlatPerfectOpenKRestrict B.obj.hom n) =
      (boundedFlatPerfectOpenKRestrict A.obj.hom n).comp (boundedFlatPerfectOpenKPullback f n) := by
  unfold boundedFlatPerfectKPullback boundedFlatPerfectOpenKRestrict boundedFlatPerfectOpenKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedFlatPerfectOpenPairIso f).symm n

/-- The original relative-open restriction is natural for arbitrary open-pair
squares when both opens and both ambient schemes are qc. -/
theorem perfectOpenKRestrict_pullback {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left] (f : A ⟶ B) (n : ℕ) :
    (perfectKPullback f.hom.hom.left n).comp (perfectOpenKRestrict B.obj.obj.hom n) =
      (perfectOpenKRestrict A.obj.obj.hom n).comp (perfectOpenKPullback f n) := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedFlatPerfectOpenToPerfectOpenKMap_bijective B.obj.obj.hom n).surjective
    x
  have h₁ := DFunLike.congr_fun (boundedFlatPerfectOpenKRestrict_comparison B.obj.obj.hom n) y
  have h₂ := DFunLike.congr_fun (perfectOpenKPullback_comp_boundedFlat f n) y
  have h₃ := DFunLike.congr_fun (perfectKPullback_comp_boundedFlat f.hom.hom.left n)
    (boundedFlatPerfectOpenKRestrict B.obj.obj.hom n y)
  have h₄ := DFunLike.congr_fun (boundedFlatPerfectOpenKRestrict_comparison A.obj.obj.hom n)
    (boundedFlatPerfectOpenKPullback f.hom n y)
  have h₅ := DFunLike.congr_fun (boundedFlatPerfectOpenKRestrict_pullback f.hom n) y
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ h₅ ⊢
  rw [h₁, h₂, h₃, h₄]
  exact congrArg (boundedFlatPerfectToPerfectKMap A.obj.obj.left n) h₅

/-- Actual ordinary restriction commutes with arbitrary open-pair pullback as well. -/
theorem perfectKRestrict_pairPullback {A B : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}}
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left] (f : A ⟶ B) (n : ℕ) :
    (perfectKPullback f.hom.hom.left n).comp (perfectKRestrict B.obj.obj.hom n) =
      (perfectKRestrict A.obj.obj.hom n).comp (perfectKPullback f.hom.hom.right n) := by
  rw [← perfectOpenKRestrict_comp_perfectOpenKMap B.obj.obj.hom,
    ← MonoidHom.comp_assoc, perfectOpenKRestrict_pullback,
    MonoidHom.comp_assoc, perfectOpenKMap_pullback,
    ← MonoidHom.comp_assoc, perfectOpenKRestrict_comp_perfectOpenKMap]

end Quillen.PerfectComplexes
