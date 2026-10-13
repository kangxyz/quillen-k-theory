/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HELP.Basic
public import Quillen.Topology.Realization.SubfamilyHEP

/-!
# Sequential composites of homotopy-extension maps

Compatible extensions are chosen recursively and glued using the universal
property of the actual topological colimit. Product with the interval preserves
this colimit. Hence a sequential composite of maps with HEP has HEP.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.TheoremA

/-- A sequential colimit of HEP maps has HEP relative to its initial stage. -/
theorem homotopyExtensionProperty_sequential
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, Quillen.homotopyExtensionProperty (F.map (homOfLE (Nat.le_succ n)))) :
    Quillen.homotopyExtensionProperty (c.ι.app 0) := by
  intro Z f H hzero
  let Extension (n : ℕ) :=
    {K : F.obj n ⊗ TopCat.I ⟶ Z // TopCat.ι₀ ≫ K = c.ι.app n ≫ f}
  have next (n : ℕ) (K : Extension n) :
      ∃ L : Extension (n + 1),
        (F.map (homOfLE (Nat.le_succ n)) ▷ TopCat.I) ≫ L.1 = K.1 := by
    have hs : TopCat.ι₀ ≫ K.1 =
        F.map (homOfLE (Nat.le_succ n)) ≫ (c.ι.app (n + 1) ≫ f) := by
      rw [← Category.assoc, c.w]
      exact K.2
    obtain ⟨L, hL₀, hL⟩ := hF n Z (c.ι.app (n + 1) ≫ f) K.1 hs
    exact ⟨⟨L, hL₀⟩, hL⟩
  let ext (n : ℕ) (K : Extension n) : Extension (n + 1) := (next n K).choose
  have hext (n : ℕ) (K : Extension n) :
      (F.map (homOfLE (Nat.le_succ n)) ▷ TopCat.I) ≫ (ext n K).1 = K.1 :=
    (next n K).choose_spec
  let K : ∀ n, Extension n := Nat.rec ⟨H, hzero⟩ (fun n K ↦ ext n K)
  have hstep (n : ℕ) :
      (F.map (homOfLE (Nat.le_succ n)) ▷ TopCat.I) ≫ (K (n + 1)).1 = (K n).1 :=
    hext n (K n)
  have hcompat {n m : ℕ} (h : n ≤ m) :
      (F.map (homOfLE h) ▷ TopCat.I) ≫ (K m).1 = (K n).1 := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
      have hsplit : (homOfLE (Nat.le.step h) : n ⟶ m + 1) =
          homOfLE h ≫ homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
      rw [hsplit, F.map_comp, comp_whiskerRight, Category.assoc, hstep, ih]
  let d : Cocone (F ⋙ tensorRight TopCat.I) := {
    pt := Z
    ι := {
      app := fun n ↦ (K n).1
      naturality := fun n m a ↦ by
        have ha : homOfLE (leOfHom a) = a := Subsingleton.elim _ _
        change (F.map a ▷ TopCat.I) ≫ (K m).1 = (K n).1 ≫ 𝟙 Z
        rw [Category.comp_id]
        simpa only [ha] using hcompat (leOfHom a) } }
  let hcI := isColimitOfPreserves (tensorRight TopCat.I) hc
  let L := hcI.desc d
  have hL (n : ℕ) : (c.ι.app n ▷ TopCat.I) ≫ L = (K n).1 := hcI.fac d n
  refine ⟨L, ?_, hL 0⟩
  apply hc.hom_ext
  intro n
  rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hL]
  exact (K n).2

end Quillen.TheoremA
