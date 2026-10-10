/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalNullHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Local lifting through quasi-isomorphisms

A map from a strict perfect complex lifts locally through an arbitrary
quasi-isomorphism, up to actual chain homotopy. The proof uses the acyclic
mapping cone, the proved local nullhomotopy theorem, and exactness of the
mapping-cone triangle in the homotopy category.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex

universe u

namespace Quillen.PerfectComplexes

/-- The cone of a quasi-isomorphism is genuinely acyclic. -/
theorem mappingCone_acyclic_of_quasiIso {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (s : K ⟶ L) [QuasiIso s] : (mappingCone s).Acyclic := by
  let P := HomotopyCategory.subcategoryAcyclic A
  have hs : P.trW ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 (inferInstanceAs (QuasiIso s))
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    ((P.trW_iff_of_distinguished (mappingCone.triangleh s)
      (HomotopyCategory.mappingCone_triangleh_distinguished s)).1 hs)

/-- Nullhomotopy after mapping into a cone produces a lift up to homotopy. -/
theorem exists_lift_of_cone_nullHomotopy {A : Type*} [Category* A] [Abelian A]
    {P K L : CochainComplex A ℤ} (s : K ⟶ L) (f : P ⟶ L)
    (h : Homotopy (f ≫ mappingCone.inr s) 0) :
    ∃ g : P ⟶ K, Nonempty (Homotopy f (g ≫ s)) := by
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hzero : Q.map f ≫ Q.map (mappingCone.inr s) = 0 := by
    rw [← Q.map_comp]
    exact (HomotopyCategory.eq_of_homotopy _ _ h).trans (Q.map_zero _ _)
  obtain ⟨g, hg⟩ := (mappingCone.triangleh s).coyoneda_exact₂
    (HomotopyCategory.mappingCone_triangleh_distinguished s) (Q.map f) hzero
  obtain ⟨g, rfl⟩ := Q.map_surjective g
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq f (g ≫ s) ?_⟩⟩
  change Q.map f = Q.map g ≫ Q.map s at hg
  exact hg.trans (Q.map_comp g s).symm

/-- A morphism from a strict perfect complex lifts locally through a
quasi-isomorphism up to an actual chain homotopy. -/
theorem exists_local_quasiIso_lift {X : Scheme.{u}} {P K L : Complex X}
    (hP : strictPerfect X P) (s : K ⟶ L) [QuasiIso s] (f : P ⟶ L) (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (hj : IsOpenImmersion j) (y : Y), j y = x ∧
      ∃ g : (@restrict Y X j hj).obj P ⟶ (@restrict Y X j hj).obj K,
        Nonempty (Homotopy ((@restrict Y X j hj).map f) (g ≫ (@restrict Y X j hj).map s)) := by
  obtain ⟨Y, j, hj, y, hy, ⟨h⟩⟩ := exists_local_nullHomotopy hP
    (f ≫ mappingCone.inr s) (mappingCone_acyclic_of_quasiIso s) x
  let := hj
  let R := Scheme.Modules.restrictFunctor j
  let e := mappingCone.mapHomologicalComplexIso s R
  have he : (restrict j).map f ≫ mappingCone.inr ((restrict j).map s) =
      (restrict j).map (f ≫ mappingCone.inr s) ≫ e.hom := by
    rw [Functor.map_comp, Category.assoc]
    exact congrArg (fun k ↦ (restrict j).map f ≫ k) (mappingCone.map_inr s R).symm
  let h' : Homotopy ((restrict j).map f ≫ mappingCone.inr ((restrict j).map s)) 0 :=
    (Homotopy.ofEq he).trans ((h.compRight e.hom).trans (Homotopy.ofEq (by simp)))
  obtain ⟨g, hg⟩ := exists_lift_of_cone_nullHomotopy ((restrict j).map s) ((restrict j).map f) h'
  exact ⟨Y, j, hj, y, hy, g, hg⟩

end Quillen.PerfectComplexes
