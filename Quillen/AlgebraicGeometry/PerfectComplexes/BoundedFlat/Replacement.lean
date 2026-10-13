/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology

/-!
# Bounded-flat replacements of cohomologically bounded perfect complexes

Actual good truncation and the proved flat replacement theorem give original
quasi-isomorphism augmentations from bounded-flat locally perfect complexes.
A genuine cohomology upper bound suffices; quasi-compactness supplies it for
all original locally perfect complexes. Maps from bounded sources factor
exactly through target good truncation. No global strict model is asserted.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.CochainComplex Quillen.SchemeSheaf
namespace Quillen.PerfectComplexes

/-- Cohomologically bounded-above locally perfect complexes admit genuine
bounded-above flat locally perfect replacements with actual augmentations. -/
theorem exists_flat_perfect_replacement_of_homology_bound {X : Scheme.{u}}
    (K : Complex X) (hK : locallyPerfect X K) (b : ℤ)
    (hb : ∀ n, b < n → IsZero (K.homology n)) :
    ∃ (P : Complex X) (p : P ⟶ K), QuasiIso p ∧ locallyPerfect X P ∧
      P.IsStrictlyLE b ∧ ∀ n, stalkwiseFlat X (P.X n) := by
  have : K.IsLE b := (CochainComplex.isLE_iff K b).mpr (fun n hn =>
    (exactAt_iff_isZero_homology _ _).mpr (hb n hn))
  let T : BoundedAboveComplex X.Modules := ⟨K.truncLE b, b, inferInstance⟩
  obtain ⟨P, p, hp, hflat, hbound⟩ :=
    exists_boundedAbove_flat_complex_replacement X T.obj b
  let : QuasiIso p := hp
  let q : P ⟶ K := p ≫ K.ιTruncLE b
  have : QuasiIso q := by dsimp [q]; infer_instance
  exact ⟨P, q, inferInstance, (locallyPerfect_iff_of_quasiIso q).mpr hK, hbound, hflat⟩

/-- Quasi-compactness supplies the honest global cohomology bound needed here. -/
theorem exists_flat_perfect_replacement_of_quasiCompact {X : Scheme.{u}} [CompactSpace X]
    (K : Perfect X) :
    ∃ (P : Complex X) (p : P ⟶ K.obj), QuasiIso p ∧ locallyPerfect X P ∧
      boundedAbove X.Modules P ∧ ∀ n, stalkwiseFlat X (P.X n) := by
  obtain ⟨a, b, hb⟩ := locallyPerfect_homology_bounded K.property
  obtain ⟨P, p, hp, hP, hbP, hflat⟩ :=
    exists_flat_perfect_replacement_of_homology_bound K.obj K.property b
      (fun n hn => hb n (Or.inr hn))
  exact ⟨P, p, hp, hP, ⟨b, hbP⟩, hflat⟩

/-- A map from an actually upper-bounded source factors exactly through good
truncation of its target at that bound, rather than merely in the derived category. -/
def mapToGoodTruncation {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] : K ⟶ L.truncLE b :=
  inv (K.ιTruncLE b) ≫ CochainComplex.truncLEMap f b

@[reassoc]
theorem mapToGoodTruncation_comp {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] : mapToGoodTruncation f b ≫ L.ιTruncLE b = f := by
  dsimp [mapToGoodTruncation]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality]
  simp

end Quillen.PerfectComplexes
