/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Quasi-isomorphisms from eventual chainwise annihilation of the kernel -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u v
namespace Quillen.HomologicalAlgebra

private theorem homologyπ_zero_iff (S : ShortComplex (ModuleCat.{u} ℤ)) (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ x : S.X₁, S.f x = S.iCycles z := by
  have he : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) :=
    congrArg (fun f => f z) S.homology_π_ι
  constructor
  · intro hz
    apply (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).mp
    rw [← he, hz, map_zero]
  · intro hz
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [map_zero, he]
    exact (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).mpr hz

/-- A degreewise surjection is a quasi-isomorphism if homologically trivial
endomorphisms over it eventually annihilate each actual kernel chain. -/
theorem quasiIso_of_eventual_kernel {J : Type v} {c : ComplexShape J}
    {K L : HomologicalComplex (ModuleCat.{u} ℤ) c} (f : K ⟶ L)
    (hf : ∀ j, Function.Surjective (f.f j)) (p : ℕ → (K ⟶ K))
    (comm : ∀ k, p k ≫ f = f)
    (hp : ∀ k j, HomologicalComplex.homologyMap (p k) j = 𝟙 _)
    (hkill : ∀ j (x : K.X j), f.f j x = 0 → ∃ k, (p k).f j x = 0) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero (HomologicalComplex.homologyMap f j).hom).mpr
    intro a ha
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ j)).mp inferInstance a
    have hn := congrArg (fun g => g z) (HomologicalComplex.homologyπ_naturality f j)
    obtain ⟨x, hx⟩ := (homologyπ_zero_iff (L.sc j) _).mp (hn.symm.trans ha)
    obtain ⟨y, hy⟩ := hf (c.prev j) x
    have hker : f.f j (K.iCycles j z - K.d (c.prev j) j y) = 0 := by
      have hc := congrArg (fun g => g y) (f.comm (c.prev j) j)
      have hz := congrArg (fun g => g z) (HomologicalComplex.cyclesMap_i f j)
      change L.iCycles j (HomologicalComplex.cyclesMap f j z) = f.f j (K.iCycles j z) at hz
      change L.d (c.prev j) j (f.f (c.prev j) y) = f.f j (K.d (c.prev j) j y) at hc
      change L.d (c.prev j) j x = L.iCycles j (HomologicalComplex.cyclesMap f j z) at hx
      rw [map_sub, ← hc, hy, hx, hz, sub_self]
    obtain ⟨k, hk⟩ := hkill j _ hker
    have hb : K.d (c.prev j) j ((p k).f (c.prev j) y) =
        K.iCycles j (HomologicalComplex.cyclesMap (p k) j z) := by
      have hc := congrArg (fun g => g y) ((p k).comm (c.prev j) j)
      have hz := congrArg (fun g => g z) (HomologicalComplex.cyclesMap_i (p k) j)
      change K.d (c.prev j) j ((p k).f (c.prev j) y) =
        (p k).f j (K.d (c.prev j) j y) at hc
      rw [map_sub, sub_eq_zero] at hk
      exact hc.trans (hk.symm.trans hz.symm)
    have hz' := (homologyπ_zero_iff (K.sc j) _).mpr ⟨_, hb⟩
    have hpn := congrArg (fun g => g z) (HomologicalComplex.homologyπ_naturality (p k) j)
    rw [hp k j] at hpn
    exact hpn.trans hz'
  · intro a
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ j)).mp inferInstance a
    obtain ⟨y, hy⟩ := hf j (L.iCycles j z)
    have hker : f.f (c.next j) (K.d j (c.next j) y) = 0 := by
      have hc := congrArg (fun g => g y) (f.comm j (c.next j))
      have hz := congrArg (fun g => g z) (L.iCycles_d j (c.next j))
      change L.d j (c.next j) (f.f j y) = f.f (c.next j) (K.d j (c.next j) y) at hc
      rw [← hc, hy]
      exact hz
    obtain ⟨k, hk⟩ := hkill (c.next j) _ hker
    have hcy : K.d j (c.next j) ((p k).f j y) = 0 :=
      (congrArg (fun g => g y) ((p k).comm j (c.next j))).trans hk
    let w := (K.sc j).cyclesMk ((p k).f j y) hcy
    have hw : K.iCycles j w = (p k).f j y := (K.sc j).i_cyclesMk _ hcy
    refine ⟨K.homologyπ j w, ?_⟩
    have hc : HomologicalComplex.cyclesMap f j w = z := by
      apply (ModuleCat.mono_iff_injective (L.iCycles j)).mp inferInstance
      have hfw := congrArg (fun g => g w) (HomologicalComplex.cyclesMap_i f j)
      have he := congrArg (fun g => g.f j y) (comm k)
      exact hfw.trans ((congrArg (f.f j) hw).trans (he.trans hy))
    have hn := congrArg (fun g => g w) (HomologicalComplex.homologyπ_naturality f j)
    exact hn.trans (congrArg (L.homologyπ j) hc)

end Quillen.HomologicalAlgebra
