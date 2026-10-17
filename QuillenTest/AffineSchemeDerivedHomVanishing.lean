/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.SchemeDerivedHomVanishing
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-! # Presentation-independent affine and original isomorphism-restriction consumers -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules (derivedRestrict)

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.AffineSchemeDerivedHomVanishing

open Quillen

/-- The constructed equivalence retains the original restriction functor literally. -/
theorem original_restriction_equivalence {U X : Scheme.{u}} (j : U ⟶ X) [IsIso j] :
    (restrictEquivalenceOfIso j).functor = restrict j := rfl

/-- Arbitrary original derived arrows, including shifted ones, are detected by an actual scheme iso.
  -/
theorem original_shifted_restriction_detection {U X : Scheme.{u}} (j : U ⟶ X) [IsIso j]
    (K L : DerivedCategory X.Modules) (n : ℤ) (φ : K⟦n⟧ ⟶ L) :
    (derivedRestrict j).map φ = 0 ↔ φ = 0 := derivedRestrict_map_eq_zero_iff j φ

/-- Top-open restriction detects the literal original unbounded derived map. -/
theorem original_top_open_detection (X : Scheme.{u}) (K L : CochainComplex X.Modules ℤ)
    (φ : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L) :
    restrictDerivedHom (⊤ : X.Opens).ι φ = 0 ↔ φ = 0 := by
  let : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact restrictDerivedHom_eq_zero_iff _ φ

/-- Every affine scheme, without a chosen presentation, has the same exact shifted cutoff. -/
theorem original_affine_adjacent_cutoff (X : Scheme.{u}) [IsAffine X]
    (P : CochainComplex X.Modules ℤ) (hP : strictPerfect X P) (M : X.Modules) [M.IsQuasicoherent]
    (b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i))
    (φ : ((DerivedCategory.Q (C := X.Modules)).obj P)⟦n⟧ ⟶ (DerivedCategory.Q (C := X.Modules)).obj
      ((_root_.CochainComplex.singleFunctor X.Modules (b-n-1)).obj M)) : φ = 0 :=
  strictPerfect_derivedHom_single_shift_eq_zero_of_isAffine X P hP M (b-n-1) b n hbound (by omega) φ

/-- On an affine open the original ambient complex may have arbitrary terms. -/
theorem original_affine_open_model (X : Scheme.{u}) (V : X.Opens) [IsAffine V.toScheme]
    (E : CochainComplex X.Modules ℤ) (P : CochainComplex V.toScheme.Modules ℤ)
      (hP : strictPerfect V.toScheme P)
    (e : (DerivedCategory.Q (C := V.toScheme.Modules)).obj P ≅
      (DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj E))
    (M : V.toScheme.Modules) [M.IsQuasicoherent]
    (a b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a+n<b)
    (φ : ((DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj E))⟦n⟧ ⟶
      (DerivedCategory.Q (C := V.toScheme.Modules)).obj
        ((_root_.CochainComplex.singleFunctor V.toScheme.Modules a).obj M))
        :
    φ = 0 :=
  derivedHom_single_shift_eq_zero_of_affine_strict_model V.toScheme _ P hP e M a b n hbound hab φ

end QuillenTest.AffineSchemeDerivedHomVanishing
