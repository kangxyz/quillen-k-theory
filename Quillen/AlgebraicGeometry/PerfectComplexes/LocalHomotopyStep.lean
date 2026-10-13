/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalLifting
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Tactic.Abel

/-!
# One local step in constructing a nullhomotopy

An approximate nullhomotopy correct above degree n can be improved to be
correct also in degree n after shrinking, provided the source term is finite
locally free and the target is exact in that degree. This is the local finite
lifting step; a bounded descending induction is still needed for a complete
local nullhomotopy theorem.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex.HomComplex

universe u

namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}} {K L : Complex X}

/-- The componentwise homotopy identity holds in degrees strictly above n. -/
def HomotopyAbove (f : K ⟶ L) (α : Cochain K L (-1)) (n : ℤ) : Prop :=
  ∀ p : ℤ, n < p → f.f p =
    α.v p (p - 1) (by omega) ≫ L.d (p - 1) p +
      K.d p (p + 1) ≫ α.v (p + 1) p (by omega)

private theorem cochain_v_heq (α : Cochain K L (-1)) (p q r : ℤ)
    (h : p + (-1) = q) (h' : p + (-1) = r) : HEq (α.v p q h) (α.v p r h') := by
  subst q
  subst r
  rfl

/-- Improve an approximate homotopy by one degree using an actual local
lift through the target's differential onto cycles. -/
theorem exists_local_homotopy_step (f : K ⟶ L) (α : Cochain K L (-1)) (n : ℤ)
    (hα : HomotopyAbove f α n) (hL : L.ExactAt n)
    [SchemeSheaf.IsFiniteLocallyFree X (K.X n)] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ β : Cochain ((restrict U.ι).obj K) ((restrict U.ι).obj L) (-1),
        HomotopyAbove ((restrict U.ι).map f) β (n - 1) := by
  let d : K.X n ⟶ L.X n := f.f n -
    α.v n (n - 1) (by omega) ≫ L.d (n - 1) n -
      K.d n (n + 1) ≫ α.v (n + 1) n (by omega)
  have hd : d ≫ L.d n (n + 1) = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, Preadditive.sub_comp]
    simp only [Category.assoc, L.d_comp_d, comp_zero, sub_zero]
    rw [f.comm, hα (n + 1) (by omega), Preadditive.comp_add]
    simp only [← Category.assoc, K.d_comp_d, zero_comp, add_zero]
    apply sub_eq_zero.mpr
    congr 2
    · omega
    · exact congrArg L.X (by omega)
    · exact cochain_v_heq α _ _ _ _ _
    · omega
  have hs : (L.sc' (n - 1) n (n + 1)).Exact :=
    (L.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 hL
  obtain ⟨U, hxU, b, hb⟩ := exists_local_factor_of_exact hs d hd x
  let R := Scheme.Modules.restrictFunctor U.ι
  change R.obj (K.X n) ⟶ R.obj (L.X (n - 1)) at b
  change b ≫ R.map (L.d (n - 1) n) = R.map d at hb
  let β : Cochain ((restrict U.ι).obj K) ((restrict U.ι).obj L) (-1) :=
    α.map R + Cochain.single b (-1)
  refine ⟨U, hxU, β, ?_⟩
  intro p hp
  have hpn : n ≤ p := by omega
  obtain rfl | hnp := hpn.eq_or_lt
  · dsimp only [β]
    rw [Cochain.add_v, Cochain.add_v, Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by
      omega)]
    simp only [Cochain.map_v, add_zero, Preadditive.add_comp]
    change R.map (f.f n) = R.map (α.v n (n - 1) _ ≫ L.d (n - 1) n) +
      b ≫ R.map (L.d (n - 1) n) + R.map (K.d n (n + 1) ≫ α.v (n + 1) n _)
    rw [hb]
    dsimp [d]
    rw [R.map_sub, R.map_sub]
    abel
  · dsimp only [β]
    rw [Cochain.add_v, Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp only [Cochain.map_v, add_zero]
    exact congrArg R.map (hα p hnp)

end Quillen.PerfectComplexes
