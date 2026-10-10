/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.OpenUnion
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Genuine finite-cover derived Hom bounds -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
variable {X : Scheme.{u}} (E L : Complex X)

/-- Vanishing of original Hom from the displayed shifted restriction. -/
def DerivedHomZeroOn (U : X.Opens) (n : ℤ) : Prop :=
  ∀ φ : ((toDerived U.toScheme).obj ((restrict U.ι).obj E))⟦n⟧ ⟶
    (toDerived U.toScheme).obj ((restrict U.ι).obj L), φ = 0

/-- Actual restriction and localization shift comparisons, in their original order. -/
def restrictDerivedShiftIso (U : X.Opens) (n : ℤ) :
    (toDerived U.toScheme).obj ((restrict U.ι).obj (E⟦n⟧)) ≅
      ((toDerived U.toScheme).obj ((restrict U.ι).obj E))⟦n⟧ :=
  (toDerived U.toScheme).mapIso (((restrict U.ι).commShiftIso n).app E) ≪≫
    ((toDerived U.toScheme).commShiftIso n).app ((restrict U.ι).obj E)

/-- Exactly one source-shift degree is lost in the actual binary union step. -/
theorem derivedHomZeroOn_union (U V : X.Opens) (n : ℤ)
    (hU : DerivedHomZeroOn E L U n) (hV : DerivedHomZeroOn E L V n)
    (hW : DerivedHomZeroOn E L (U ⊓ V) (n + 1)) :
    DerivedHomZeroOn E L (U ⊔ V) n := by
  intro φ
  apply hom_eq_zero_of_iso (restrictDerivedShiftIso E (U ⊔ V) n).symm (Iso.refl _)
    (fun ψ => derivedHom_eq_zero_on_openUnion (E⟦n⟧) L U V ?_ ?_ ?_ ψ) φ
  · exact hom_eq_zero_of_iso (restrictDerivedShiftIso E U n) (Iso.refl _) hU
  · exact hom_eq_zero_of_iso (restrictDerivedShiftIso E V n) (Iso.refl _) hV
  · exact hom_eq_zero_of_iso
      ((shiftFunctor (Derived (U ⊓ V).toScheme) (1 : ℤ)).mapIso
        (restrictDerivedShiftIso E (U ⊓ V) n) ≪≫
        ((shiftFunctorAdd (Derived (U ⊓ V).toScheme) n 1).app
          ((toDerived (U ⊓ V).toScheme).obj ((restrict (U ⊓ V).ι).obj E))).symm)
      (Iso.refl _) hW

/-- The actual empty open has zero derived Hom in every source shift. -/
theorem derivedHomZeroOn_bot (n : ℤ) : DerivedHomZeroOn E L ⊥ n := by
  have hE : IsZero ((restrict (⊥ : X.Opens).ι).obj E) := by
    rw [IsZero.iff_id_eq_zero]
    ext i : 1
    have hz : IsZero (((restrict (⊥ : X.Opens).ι).obj E).X i) := by
      rw [SchemeSheaf.isZero_iff_stalks]
      intro x
      exact False.elim x.property
    exact hz.eq_of_src _ _
  exact fun φ => ((shiftFunctor (Derived (⊥ : X.Opens).toScheme) n).map_isZero
    ((toDerived (⊥ : X.Opens).toScheme).map_isZero hE)).eq_of_src φ 0

/-- A finite inf-closed cover loses at most one allowed source-shift degree per
additional open. The empty family is included, with its actual zero Hom. -/
theorem derivedHomZeroOn_finite_union (B : Set X.Opens)
    (hB : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B) (b : ℤ)
    (hlocal : ∀ U ∈ B, ∀ n : ℤ, n < b → DerivedHomZeroOn E L U n)
    (s : Finset X.Opens) (hs : ∀ U ∈ s, U ∈ B)
    (n : ℤ) (hn : n + (s.card : ℤ) - 1 < b) :
    DerivedHomZeroOn E L (s.sup id) n := by
  classical
  induction hc : s.card using Nat.strong_induction_on generalizing s n with
  | h m ih =>
    by_cases hz : s = ∅
    · subst s
      simpa using derivedHomZeroOn_bot E L n
    obtain ⟨U, hU⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    let t := s.erase U
    have hins : insert U t = s := Finset.insert_erase hU
    have hcard : t.card + 1 = s.card := Finset.card_erase_add_one hU
    have hlt : t.card < m := by omega
    have htB : ∀ V ∈ t, V ∈ B := fun V hV => hs V (Finset.mem_of_mem_erase hV)
    let q := t.image (fun V => U ⊓ V)
    have hqcard : q.card ≤ t.card := Finset.card_image_le
    have hqB : ∀ V ∈ q, V ∈ B := by
      intro V hV
      change V ∈ t.image (fun V => U ⊓ V) at hV
      obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hV
      exact hB U (hs U hU) Z (htB Z hZ)
    have hUn := hlocal U (hs U hU) n (by omega)
    have htn := ih t.card hlt t htB n (by omega) rfl
    have hqn := ih q.card (by omega) q hqB (n+1) (by omega) rfl
    have hqi : q.sup id = U ⊓ t.sup id := by
      simp only [q, Finset.sup_image, Function.comp_def, id_eq]
      exact (Finset.sup_inf_distrib_left t id U).symm
    rw [hqi] at hqn
    have hout := derivedHomZeroOn_union E L U (t.sup id) n hUn htn hqn
    have hsup : U ⊔ t.sup id = s.sup id := by
      rw [← hins, Finset.sup_insert, id_eq]
    rwa [hsup] at hout

end Quillen.PerfectComplexes
