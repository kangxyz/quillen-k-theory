/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.TotalTriangular
public import Quillen.Algebra.Homology.EventualKernelComparison
public import Mathlib.Algebra.Homology.Homotopy

/-! # The finite triangular comparison argument for actual total maps -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.HomologicalAlgebra

variable {K : HomologicalComplex₂ (ModuleCat.{u} ℤ)
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}

/-- A homotopically trivial triangular defect proves the original map is a quasi-isomorphism. -/
theorem quasiIso_of_total_triangular
    (f : K.total (ComplexShape.down ℕ) ⟶ L)
    (s : ∀ n, L.X n ⟶ (K.total (ComplexShape.down ℕ)).X n)
    (hs : ∀ n, s n ≫ f.f n = 𝟙 _)
    (t : K.total (ComplexShape.down ℕ) ⟶ K.total (ComplexShape.down ℕ))
    (ht : Homotopy (𝟙 _) t) (hcomm : t ≫ f = f)
    (hlower : ∀ n (p q : TotalDegree n), p.val.1 ≤ q.val.1 →
      totalSummand K n p ≫ (t.f n - f.f n ≫ s n) ≫ totalCoordinate K n q = 0) :
    QuasiIso f := by
  refine quasiIso_of_eventual_kernel f ?_ (totalIterate t) ?_ ?_ ?_
  · intro n y
    exact ⟨s n y, congrArg (fun a ↦ a y) (hs n)⟩
  · intro k
    induction k with
    | zero => simp
    | succ k ih => rw [totalIterate_succ, Category.assoc, ih, hcomm]
  · intro k n
    have ht' : HomologicalComplex.homologyMap t n = 𝟙 _ :=
      (ht.homologyMap_eq n).symm.trans (HomologicalComplex.homologyMap_id _ n)
    induction k with
    | zero => simp
    | succ k ih =>
      rw [totalIterate_succ, HomologicalComplex.homologyMap_comp, ht', ih, Category.id_comp]
  · exact totalIterate_eventually_zero f t s hcomm hlower

end Quillen.HomologicalAlgebra
