/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullback
/-! # Bijectivity of original K-pullbacks along scheme isomorphisms -/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Original strict pullback along a scheme isomorphism is bijective. -/
lemma strictKPullback_iso_bijective {X Y : Scheme.{u}} (e : X ≅ Y) (n : ℕ) :
    Function.Bijective (strictKPullback e.hom n) := by
  have hi : Function.LeftInverse (strictKPullback e.inv n) (strictKPullback e.hom n) := by
    intro x
    have h : (strictKPullback e.inv n).comp (strictKPullback e.hom n) = MonoidHom.id _ := by
      rw [← strictKPullback_comp, e.inv_hom_id, strictKPullback_id]
    exact DFunLike.congr_fun h x
  have hj : Function.RightInverse (strictKPullback e.inv n) (strictKPullback e.hom n) := by
    intro x
    have h : (strictKPullback e.hom n).comp (strictKPullback e.inv n) = MonoidHom.id _ := by
      rw [← strictKPullback_comp, e.hom_inv_id, strictKPullback_id]
    exact DFunLike.congr_fun h x
  exact ⟨hi.injective,hj.surjective⟩

/-- Original perfect pullback along an isomorphism of qc schemes is bijective. -/
lemma perfectKPullback_iso_bijective {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (e : X ≅ Y) (n : ℕ) : Function.Bijective (perfectKPullback e.hom n) := by
  have hi : Function.LeftInverse (perfectKPullback e.inv n) (perfectKPullback e.hom n) := by
    intro x
    have h : (perfectKPullback e.inv n).comp (perfectKPullback e.hom n) = MonoidHom.id _ := by
      rw [← perfectKPullback_comp, e.inv_hom_id, perfectKPullback_id]
    exact DFunLike.congr_fun h x
  have hj : Function.RightInverse (perfectKPullback e.inv n) (perfectKPullback e.hom n) := by
    intro x
    have h : (perfectKPullback e.hom n).comp (perfectKPullback e.inv n) = MonoidHom.id _ := by
      rw [← perfectKPullback_comp, e.hom_inv_id, perfectKPullback_id]
    exact DFunLike.congr_fun h x
  exact ⟨hi.injective,hj.surjective⟩

end Quillen.PerfectComplexes
