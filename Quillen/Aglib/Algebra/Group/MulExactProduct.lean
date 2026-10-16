/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.FiveLemma

/-!
# Original product group exactness and pair shuffle

The literal four-factor shuffle is a group isomorphism and two copies of the original
exact group row remain exact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
/-- Explicit rearrangement of the two original T-first local pairs into pairs of coefficients. -/
def localPairShuffle (A : Type u) (B : Type v) [Group A] [Group B] :
    (A × B) × (A × B) ≃* (A × A) × (B × B) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Two copies of an actual exact group row remain exact. -/
theorem mulExact_prodMap {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    Function.MulExact (f.prodMap f) (g.prodMap g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (h x.1).mp (congrArg _root_.Prod.fst hx)
    obtain ⟨b, hb⟩ := (h x.2).mp (congrArg _root_.Prod.snd hx)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨a, rfl⟩
    exact Prod.ext (h.apply_apply_eq_one a.1) (h.apply_apply_eq_one a.2)


end Quillen.PerfectComplexes.ProjectiveLine.NativeMayerVietoris
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
namespace Quillen.PerfectComplexes.ProjectiveLine
theorem mulExact_prodMap {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    Function.MulExact (f.prodMap f) (g.prodMap g) := by
  rintro ⟨a, b⟩
  change (g a, g b) = (1, 1) ↔ ∃ x : A × A, (f x.1, f x.2) = (a, b)
  constructor
  · intro hab
    obtain ⟨x, hx⟩ := (h a).mp (congrArg Prod.fst hab)
    obtain ⟨y, hy⟩ := (h b).mp (congrArg Prod.snd hab)
    exact ⟨(x, y), Prod.ext hx hy⟩
  · rintro ⟨⟨x, y⟩, hxy⟩
    have hx : f x = a := congrArg Prod.fst hxy
    have hy : f y = b := congrArg Prod.snd hxy
    rw [← hx, ← hy]
    exact Prod.ext (h.apply_apply_eq_one x) (h.apply_apply_eq_one y)


end Quillen.PerfectComplexes.ProjectiveLine
end
end
