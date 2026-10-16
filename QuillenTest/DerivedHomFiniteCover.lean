/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.FiniteCover
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Original-map and degree-bound consumers for derived Hom descent -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace QuillenTest.DerivedHomFiniteCover
attribute [local instance] HasDerivedCategory.standard

/-- Actual local homotopy equivalences force the unchanged global arrow weak,
for an arbitrarily indexed family of covering open immersions. -/
theorem original_arrow_weak_of_local_homotopyEquivalences {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) {ι : Type v} (Y : ι → Scheme.{u})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x)
    (e : ∀ i, HomotopyEquiv ((restrict (j i)).obj K) ((restrict (j i)).obj L))
    (he : ∀ i, (e i).hom = (restrict (j i)).map f) : QuasiIso f := by
  apply quasiIso_of_openImmersionCover f Y j hj
  intro i
  rw [← he i]
  exact (e i).quasiIso_hom

/-- Local equality of the original derived maps gives global equality when the
actual shifted-overlap obstruction vanishes. -/
theorem original_binary_maps_equal {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (E L : CochainComplex X.Modules ℤ)
    (hW : ∀ γ : ((DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
        ((restrict (pullback.fst U.ι V.ι)).obj ((restrict U.ι).obj E)))⟦(1 : ℤ)⟧ ⟶
      (DerivedCategory.Q (C := (pullback U.ι V.ι).Modules)).obj
        ((restrict (pullback.fst U.ι V.ι)).obj ((restrict U.ι).obj L)), γ = 0)
    (φ ψ : (DerivedCategory.Q (C := X.Modules)).obj E ⟶ (DerivedCategory.Q (C := X.Modules)).obj L)
    (hU : restrictDerivedHom U.ι φ = restrictDerivedHom U.ι ψ)
    (hV : restrictDerivedHom V.ι φ = restrictDerivedHom V.ι ψ) : φ = ψ := by
  apply sub_eq_zero.mp
  apply derivedHom_eq_zero_of_binaryOpenCover U V hUV E L hW (φ - ψ)
  · simpa only [restrictDerivedHom, Functor.map_sub, Preadditive.comp_sub,
      Preadditive.sub_comp] using sub_eq_zero.mpr hU
  · simpa only [restrictDerivedHom, Functor.map_sub, Preadditive.comp_sub,
      Preadditive.sub_comp] using sub_eq_zero.mpr hV

/-- The empty open admits exactly one original derived map in every integer shift. -/
theorem empty_open_unique_shifted_map {X : Scheme.{u}} (E L : CochainComplex X.Modules ℤ) (n : ℤ) :
    ∃! _φ : ((DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
      ((restrict (⊥ : X.Opens).ι).obj E))⟦n⟧ ⟶
      (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
        ((restrict (⊥ : X.Opens).ι).obj L), True :=
  ⟨0, trivial, fun φ _ => derivedHomZeroOn_bot E L n φ⟩

/-- The two-open step visibly requires the next source shift on the intersection. -/
theorem two_open_unshifted_detection {X : Scheme.{u}} (E L : CochainComplex X.Modules ℤ)
    (U V : X.Opens)
    (hU : DerivedHomZeroOn E L U 0) (hV : DerivedHomZeroOn E L V 0)
    (hW : DerivedHomZeroOn E L (U ⊓ V) 1) : DerivedHomZeroOn E L (U ⊔ V) 0 := by
  exact derivedHomZeroOn_union E L U V 0 hU hV hW

/-- Any larger chosen cardinality bound still controls the exact original finite union. -/
theorem original_union_bound_of_card_le {X : Scheme.{u}} (E L : CochainComplex X.Modules ℤ)
    (B : Set X.Opens) (hB : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B) (b : ℤ)
    (hlocal : ∀ U ∈ B, ∀ n : ℤ, n < b → DerivedHomZeroOn E L U n)
    (s : Finset X.Opens) (hs : ∀ U ∈ s, U ∈ B) (N : ℕ) (hN : s.card ≤ N)
    (n : ℤ) (hn : n + N - 1 < b) : DerivedHomZeroOn E L (s.sup id) n :=
  derivedHomZeroOn_finite_union E L B hB b hlocal s hs n (by omega)

/-- A nonzero original map detects the precise remaining finite-cover degree obstruction. -/
theorem nonzero_original_map_degree_obstruction {X : Scheme.{u}} (E L : CochainComplex X.Modules ℤ)
    (B : Set X.Opens) (hB : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B) (b : ℤ)
    (hlocal : ∀ U ∈ B, ∀ n : ℤ, n < b → DerivedHomZeroOn E L U n)
    (s : Finset X.Opens) (hs : ∀ U ∈ s, U ∈ B) (n : ℤ)
    (φ : ((DerivedCategory.Q (C := (s.sup id).toScheme.Modules)).obj
      ((restrict (s.sup id).ι).obj E))⟦n⟧ ⟶
      (DerivedCategory.Q (C := (s.sup id).toScheme.Modules)).obj ((restrict (s.sup id).ι).obj L))
        (hφ : φ ≠ 0) :
    b ≤ n + (s.card : ℤ) - 1 := by
  by_contra h
  exact hφ (derivedHomZeroOn_finite_union E L B hB b hlocal s hs n (by omega) φ)

end QuillenTest.DerivedHomFiniteCover
