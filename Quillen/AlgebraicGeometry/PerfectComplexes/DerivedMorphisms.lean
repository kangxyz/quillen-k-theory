/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalQuasiIsoLifting
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Local chain representatives for derived morphisms

The Gabriel–Zisman localization used for local perfectness is the standard
model of mathlib's derived category. Its fraction theorem, combined with
local quasi-isomorphism lifting, gives actual chain representatives near
each point for derived maps with strict perfect source.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}}

/-- The actual localization identifies chain-homotopic maps. -/
theorem toDerived_map_eq_of_homotopy {K L : Complex X} {f g : K ⟶ L} (h : Homotopy f g) :
    (toDerived X).map f = (toDerived X).map g := by
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  exact DerivedCategory.Q_map_eq_of_homotopy X.Modules h

/-- A morphism in the actual localization has a chain-level left fraction,
with the denominator proved to be a quasi-isomorphism. -/
theorem toDerived_left_fraction {K L : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    ∃ (M : Complex X) (g : K ⟶ M) (s : L ⟶ M),
      QuasiIso s ∧ φ ≫ (toDerived X).map s = (toDerived X).map g := by
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  change DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L at φ
  obtain ⟨M, g, s, hs, hφ⟩ := DerivedCategory.left_fac φ
  let := hs
  refine ⟨M, g, s, (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules s).1 hs, ?_⟩
  change φ ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map g
  rw [hφ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction of a derived morphism, expressed at the actual restricted
complexes using the localization factorization isomorphism. -/
def restrictDerivedHom {K L : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    (toDerived U).obj ((restrict j).obj K) ⟶ (toDerived U).obj ((restrict j).obj L) :=
  (derivedRestrictFactors j).inv.app K ≫ (derivedRestrict j).map φ ≫
    (derivedRestrictFactors j).hom.app L

/-- Restricted derived morphisms compose as actual morphisms. -/
@[simp]
theorem restrictDerivedHom_comp {K L M : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L)
    (ψ : (toDerived X).obj L ⟶ (toDerived X).obj M) :
    restrictDerivedHom j (φ ≫ ψ) = restrictDerivedHom j φ ≫ restrictDerivedHom j ψ := by
  simp [restrictDerivedHom, Functor.map_comp, Category.assoc]

/-- Restriction of a localized chain map is localization of its actual
restriction. -/
@[simp]
theorem restrictDerivedHom_map {K L : Complex X} (f : K ⟶ L) :
    restrictDerivedHom j ((toDerived X).map f) = (toDerived U).map ((restrict j).map f) := by
  have h := (derivedRestrictFactors j).hom.naturality f
  change (derivedRestrict j).map ((toDerived X).map f) ≫
    (derivedRestrictFactors j).hom.app L =
      (derivedRestrictFactors j).hom.app K ≫ (toDerived U).map ((restrict j).map f) at h
  unfold restrictDerivedHom
  rw [h]
  simp

/-- Every derived morphism with strict perfect source is represented by an
actual chain map after restricting around any chosen point. -/
theorem exists_local_chain_representative {P L : Complex X} (hP : strictPerfect X P)
    (φ : (toDerived X).obj P ⟶ (toDerived X).obj L) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      ∃ g : (@restrict Y X j hj).obj P ⟶ (@restrict Y X j hj).obj L,
        @restrictDerivedHom X Y j hj P L φ = (toDerived Y).map g := by
  obtain ⟨M, f, s, hs, hφ⟩ := toDerived_left_fraction φ
  let := hs
  obtain ⟨Y, j, hj, y, hy, g, ⟨h⟩⟩ := exists_local_quasiIso_lift hP s f x
  let := hj
  refine ⟨Y, j, hj, y, hy, g, ?_⟩
  apply (cancel_mono ((toDerived Y).map ((restrict j).map s))).1
  have hφ' := congrArg (restrictDerivedHom j) hφ
  rw [restrictDerivedHom_comp, restrictDerivedHom_map, restrictDerivedHom_map] at hφ'
  exact hφ'.trans ((toDerived_map_eq_of_homotopy h).trans ((toDerived Y).map_comp _ _))

end Quillen.PerfectComplexes
