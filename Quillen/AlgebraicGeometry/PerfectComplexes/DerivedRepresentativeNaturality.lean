/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedMorphisms

/-!
# Local representatives are independent of the chosen derived restriction lift

The local chain representative is compatible with every functor realizing
restriction on the quasi-isomorphism localization. In particular it can be
used with mathlib's triangulated derived restriction, not only the directly
constructed Gabriel–Zisman lift.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Quillen.PerfectComplexes

variable {X Y : Scheme.{u}} {R : Complex X ⥤ Complex Y}
    {F : Derived X ⥤ Derived Y} (e : toDerived X ⋙ F ≅ R ⋙ toDerived Y)

/-- A derived functor expressed at the localized chain objects through its
specified factorization isomorphism. -/
def liftedDerivedHom {K L : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    (toDerived Y).obj (R.obj K) ⟶ (toDerived Y).obj (R.obj L) :=
  e.inv.app K ≫ F.map φ ≫ e.hom.app L

@[simp]
theorem liftedDerivedHom_comp {K L M : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L)
    (ψ : (toDerived X).obj L ⟶ (toDerived X).obj M) :
    liftedDerivedHom e (φ ≫ ψ) = liftedDerivedHom e φ ≫ liftedDerivedHom e ψ := by
  simp [liftedDerivedHom, Functor.map_comp, Category.assoc]

@[simp]
theorem liftedDerivedHom_map {K L : Complex X} (f : K ⟶ L) :
    liftedDerivedHom e ((toDerived X).map f) = (toDerived Y).map (R.map f) := by
  have h := e.hom.naturality f
  change F.map ((toDerived X).map f) ≫ e.hom.app L =
    e.hom.app K ≫ (toDerived Y).map (R.map f) at h
  unfold liftedDerivedHom
  rw [h]
  simp

/-- The constructed chain representative works for every derived lift of
the actual open restriction functor, including its triangulated model. -/
theorem exists_local_chain_representative_any_lift {P L : Complex X} (hP : strictPerfect X P)
    (φ : (toDerived X).obj P ⟶ (toDerived X).obj L) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      ∃ g : (@restrict Y X j hj).obj P ⟶ (@restrict Y X j hj).obj L,
        ∀ (F : Derived X ⥤ Derived Y)
          (e : toDerived X ⋙ F ≅ @restrict Y X j hj ⋙ toDerived Y),
            liftedDerivedHom e φ = (toDerived Y).map g := by
  obtain ⟨M, f, s, hs, hφ⟩ := toDerived_left_fraction φ
  let := hs
  obtain ⟨Y, j, hj, y, hy, g, ⟨h⟩⟩ := exists_local_quasiIso_lift hP s f x
  let := hj
  refine ⟨Y, j, hj, y, hy, g, fun F e ↦ ?_⟩
  apply (cancel_mono ((toDerived Y).map ((restrict j).map s))).1
  have hφ' := congrArg (liftedDerivedHom e) hφ
  rw [liftedDerivedHom_comp, liftedDerivedHom_map, liftedDerivedHom_map] at hφ'
  exact hφ'.trans ((toDerived_map_eq_of_homotopy h).trans ((toDerived Y).map_comp _ _))

end Quillen.PerfectComplexes
