/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Cylinder
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RelativeFlatFactorization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Replacement
public import Quillen.Waldhausen.Approximation.Basic

/-!
# Genuine approximation by the bounded-flat perfect model

For the original inclusion into locally perfect complexes, App1 is literal
reflection of quasi-isomorphisms. Actual target good truncation and relative
flat factorization prove App2 with its original commuting triangle and an
actual admissible cofibration. The quotient is locally perfect by the proved
mapping-cone-to-quotient quasi-isomorphism. Quasi-compactness supplies the
uniform cohomology bound; no approximation or K-equivalence is assumed.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.CochainComplex Quillen.SchemeSheaf
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- The genuine bounded-flat inclusion satisfies the relative factorization
condition whenever the original target has an honest cohomology upper bound. -/
theorem boundedFlatPerfect_relative_factorization_of_bound {X : Scheme.{u}}
    (K : BoundedFlatPerfect X) (L : Perfect X)
    (f : (boundedFlatPerfectInclusion X).obj K ⟶ L) (b : ℤ)
    [K.obj.IsStrictlyLE b] [L.obj.IsLE b] :
    ∃ (M : BoundedFlatPerfect X) (i : K ⟶ M)
      (p : (boundedFlatPerfectInclusion X).obj M ⟶ L),
      (boundedFlatPerfectWaldhausen X).cof i ∧ (perfectWaldhausen X).weq p ∧
        (boundedFlatPerfectInclusion X).map i ≫ p = f := by
  let s : K.obj ⟶ L.obj := f.hom
  let fT := mapToGoodTruncation s b
  obtain ⟨M, Q, i, p₀, q, w, hp₀, hfac, hS, hbM, hbQ, hMflat, hQflat⟩ :=
    exists_boundedAbove_relative_flat_factorization X fT b K.property.2.2
  let : QuasiIso p₀ := hp₀
  let p : M ⟶ L.obj := p₀ ≫ L.obj.ιTruncLE b
  have hp : QuasiIso p := by dsimp [p]; infer_instance
  have hMp : locallyPerfect X M := (locallyPerfect_iff_of_quasiIso p).mpr L.property
  let S := ShortComplex.mk i q w
  have hQp : locallyPerfect X Q := by
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
    exact (locallyPerfect_iff_of_quasiIso (CochainComplex.mappingCone.descShortComplex S)).mp
      (locallyPerfect_mappingCone K.property.1 hMp i)
  let M' : BoundedFlatPerfect X := ⟨M, hMp, ⟨b + 1, hbM⟩, hMflat⟩
  let i' : K ⟶ M' := ObjectProperty.homMk i
  let p' : (boundedFlatPerfectInclusion X).obj M' ⟶ L := ObjectProperty.homMk p
  refine ⟨M', i', p', ?_, hp, ?_⟩
  · exact (ExactSubcategory.inflation_iff (abelianExactStructure (Complex X))
      (boundedFlatPerfect X) i').mpr ⟨Q, ⟨hQp, ⟨b + 1, hbQ⟩, hQflat⟩, q, w, hS⟩
  · apply ObjectProperty.hom_ext
    change i ≫ (p₀ ≫ L.obj.ιTruncLE b) = f.hom
    rw [← Category.assoc, hfac]
    exact mapToGoodTruncation_comp s b

/-- Quasi-compactness supplies actual bounds, and relative projective-presheaf
factorization supplies the original App2 commuting triangle. No K-equivalence is assumed. -/
theorem boundedFlatPerfectInclusion_approximation (X : Scheme.{u}) [CompactSpace X] :
    Waldhausen.HasApproximationProperty (boundedFlatPerfectWaldhausen X)
      (perfectWaldhausen X) (boundedFlatPerfectInclusion X) where
  reflects _ h := h
  lift {K L} f := by
    obtain ⟨a, b, hb⟩ := locallyPerfect_homology_bounded L.property
    obtain ⟨c, hc⟩ := K.property.2.1
    have : K.obj.IsStrictlyLE (max c b) := K.obj.isStrictlyLE_of_le c _ (le_max_left _ _)
    have : L.obj.IsLE (max c b) := (CochainComplex.isLE_iff _ _).mpr (fun n hn =>
      (exactAt_iff_isZero_homology _ _).mpr (hb n (Or.inr (by omega))))
    exact boundedFlatPerfect_relative_factorization_of_bound K L f (max c b)

end Quillen.PerfectComplexes
