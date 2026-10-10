/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedMorphisms

/-! # Original right fractions and restriction of derived isomorphisms -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {X : Scheme.{u}}

/-- An arbitrary original derived morphism has an actual weak source denominator. -/
theorem toDerived_right_fraction {K L : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    ∃ (M : Complex X) (s : M ⟶ K) (p : M ⟶ L),
      QuasiIso s ∧ (toDerived X).map s ≫ φ = (toDerived X).map p := by
  let : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
  obtain ⟨M, s, hs, p, hφ⟩ := DerivedCategory.right_fac φ
  let := hs
  refine ⟨M, s, p, (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules s).1 hs, ?_⟩
  change DerivedCategory.Q.map s ≫ φ = DerivedCategory.Q.map p
  rw [hφ, IsIso.hom_inv_id_assoc]

variable {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

@[simp]
theorem restrictDerivedHom_id (K : Complex X) :
    restrictDerivedHom j (𝟙 ((toDerived X).obj K)) =
      𝟙 ((toDerived Y).obj ((restrict j).obj K)) := by
  simp [restrictDerivedHom]

@[simp]
theorem restrictDerivedIso_hom {K L : Complex X}
    (e : (toDerived X).obj K ≅ (toDerived X).obj L) :
    (restrictDerivedIso j e).hom = restrictDerivedHom j e.hom := rfl

@[simp]
theorem restrictDerivedIso_inv {K L : Complex X}
    (e : (toDerived X).obj K ≅ (toDerived X).obj L) :
    (restrictDerivedIso j e).inv = restrictDerivedHom j e.inv := by
  simp [restrictDerivedIso, restrictDerivedHom, Category.assoc]

@[simp]
theorem restrictDerivedIso_asIso_map {K L : Complex X} (s : K ⟶ L) [QuasiIso s] :
    restrictDerivedIso j (asIso ((toDerived X).map s)) =
      asIso ((toDerived Y).map ((restrict j).map s)) := by
  apply Iso.ext
  exact restrictDerivedHom_map j s

@[simp]
theorem restrictDerivedHom_inv_map {K L : Complex X} (s : K ⟶ L) [QuasiIso s] :
    restrictDerivedHom j (inv ((toDerived X).map s)) =
      inv ((toDerived Y).map ((restrict j).map s)) := by
  simpa only [restrictDerivedIso_inv, asIso_inv] using
    congrArg Iso.inv (restrictDerivedIso_asIso_map j s)

end Quillen.PerfectComplexes
