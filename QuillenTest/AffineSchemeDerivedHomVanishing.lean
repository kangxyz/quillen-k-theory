/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SchemeDerivedHomVanishing

/-! # Presentation-independent affine and original isomorphism-restriction consumers -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.AffineSchemeDerivedHomVanishing

open Quillen

/-- The constructed equivalence retains the original restriction functor literally. -/
theorem original_restriction_equivalence {U X : Scheme.{u}} (j : U ⟶ X) [IsIso j] :
    (restrictEquivalenceOfIso j).functor = restrict j := rfl

/-- Arbitrary original derived arrows, including shifted ones, are detected by an actual scheme iso.
  -/
theorem original_shifted_restriction_detection {U X : Scheme.{u}} (j : U ⟶ X) [IsIso j]
    (K L : Derived X) (n : ℤ) (φ : K⟦n⟧ ⟶ L) :
    (derivedRestrict j).map φ = 0 ↔ φ = 0 := derivedRestrict_map_eq_zero_iff j φ

/-- Top-open restriction detects the literal original unbounded derived map. -/
theorem original_top_open_detection (X : Scheme.{u}) (K L : Complex X)
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    restrictDerivedHom (⊤ : X.Opens).ι φ = 0 ↔ φ = 0 := by
  let : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact restrictDerivedHom_eq_zero_iff _ φ

/-- Every affine scheme, without a chosen presentation, has the same exact shifted cutoff. -/
theorem original_affine_adjacent_cutoff (X : Scheme.{u}) [IsAffine X]
    (P : Complex X) (hP : strictPerfect X P) (M : X.Modules) [M.IsQuasicoherent]
    (b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i))
    (φ : ((toDerived X).obj P)⟦n⟧ ⟶ (toDerived X).obj
      ((_root_.CochainComplex.singleFunctor X.Modules (b-n-1)).obj M)) : φ = 0 :=
  strictPerfect_derivedHom_single_shift_eq_zero_of_isAffine X P hP M (b-n-1) b n hbound (by omega) φ

/-- On an affine open the original ambient complex may have arbitrary terms. -/
theorem original_affine_open_model (X : Scheme.{u}) (V : X.Opens) [IsAffine V.toScheme]
    (E : Complex X) (P : Complex V.toScheme) (hP : strictPerfect V.toScheme P)
    (e : (toDerived V.toScheme).obj P ≅ (toDerived V.toScheme).obj ((restrict V.ι).obj E))
    (M : V.toScheme.Modules) [M.IsQuasicoherent]
    (a b n : ℤ) (hbound : ∀ i, i < b → IsZero (P.X i)) (hab : a+n<b)
    (φ : ((toDerived V.toScheme).obj ((restrict V.ι).obj E))⟦n⟧ ⟶
      (toDerived V.toScheme).obj ((_root_.CochainComplex.singleFunctor V.toScheme.Modules a).obj M))
        :
    φ = 0 :=
  derivedHom_single_shift_eq_zero_of_affine_strict_model V.toScheme _ P hP e M a b n hbound hab φ

end QuillenTest.AffineSchemeDerivedHomVanishing
