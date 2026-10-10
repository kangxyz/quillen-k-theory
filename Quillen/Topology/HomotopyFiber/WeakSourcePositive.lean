/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyFiber.GroupDetection

/-! # Weak source changes on positive homotopy groups of the actual fibers

The original source-change fiber map retains the base path. A direct five-term
LES argument uses the original total-space maps in the two adjacent degrees.
The separate zeroth homotopy-set assertion is not assumed or claimed here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace Quillen.HomotopyFiber
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (sq : g.comp u = f)
  (x : X) (b : B) (hx : f x = b)

/-- Bijection on the original total groups in degree n+1 and surjection in
degree n+2 give bijection on the original fiber group in degree n+1. -/
theorem piMap_mapOver_bijective (n : ℕ)
    (hcurrent : Function.Bijective (piMap n u (x := x) rfl))
    (hnext : Function.Surjective (piMap (n + 1) u (x := x) rfl)) :
    Function.Bijective (piMap n (mapOver f g u sq b)
      (mapOver_basepoint f g u sq x b hx)) := by
  let hy := (ContinuousMap.congr_fun sq x).trans hx
  let v := piMap n (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx)
  let i₁ := piMap n (projection f b) (projection_basepoint f b x hx)
  let i₂ := piMap n (projection g b) (projection_basepoint g b (u x) hy)
  let p₁ := piMap n f hx
  let p₂ := piMap n g hy
  let m := piMap n u (x := x) rfl
  have wi (a) : m (i₁ a) = i₂ (v a) :=
    homotopyGroupMap_projection_natural u (ContinuousMap.id B) sq.symm x b hx a
  have wp (a) : p₂ (m a) = p₁ a := by
    have h := homotopyGroupMap_square_natural u (ContinuousMap.id B) sq.symm x b hx a
    rw [homotopyGroupMap_id] at h
    exact h.symm
  have wd (a) : v (connectingHom f b x hx n a) = connectingHom g b (u x) hy n a := by
    have h := connectingMap_natural u (ContinuousMap.id B) sq.symm x b hx (n + 1) a
    rw [homotopyGroupMap_id] at h
    exact h
  constructor
  · apply (injective_iff_map_eq_one v).2
    intro a ha
    have hi : i₁ a = 1 := hcurrent.injective (by rw [wi, ha, map_one, map_one])
    have hmem : a ∈ (connectingHom f b x hx n).range := by
      rw [range_connectingHom_eq_ker_projection]
      exact hi
    obtain ⟨d, hd⟩ := hmem
    have hδ : connectingHom g b (u x) hy n d = 1 := by rw [← wd, hd]; exact ha
    have hp : d ∈ (piMap (n + 1) g hy).range := by
      rw [range_piMap_eq_ker_connectingHom]
      exact hδ
    obtain ⟨y, hy'⟩ := hp
    obtain ⟨z, hz⟩ := hnext y
    have hz' : piMap (n + 1) f hx z = d := by
      have h := homotopyGroupMap_square_natural u (ContinuousMap.id B) sq.symm x b hx z
      rw [homotopyGroupMap_id] at h
      exact h.trans ((congrArg (piMap (n + 1) g hy) hz).trans hy')
    have hδ' : connectingHom f b x hx n d = 1 := by
      have hmem : d ∈ (piMap (n + 1) f hx).range := ⟨z, hz'⟩
      rw [range_piMap_eq_ker_connectingHom] at hmem
      exact hmem
    rw [hd] at hδ'
    exact hδ'
  · intro a
    obtain ⟨c, hc⟩ := hcurrent.surjective (i₂ a)
    have hp : p₁ c = 1 := by
      rw [← wp, hc]
      exact DFunLike.congr_fun (homotopyGroupMapHom_projection_comp g b (u x) hy) a
    obtain ⟨d, hd⟩ := (mem_range_projection_iff f b x hx c).2 hp
    have hi : i₂ (a * (v d)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← wi, hd, hc, mul_inv_cancel]
    have hm : a * (v d)⁻¹ ∈ (connectingHom g b (u x) hy n).range := by
      rw [range_connectingHom_eq_ker_projection]
      exact hi
    obtain ⟨e, he⟩ := hm
    refine ⟨connectingHom f b x hx n e * d, ?_⟩
    change v (connectingHom f b x hx n e * d) = a
    rw [map_mul, wd, he, inv_mul_cancel_right]

end Quillen.HomotopyFiber
