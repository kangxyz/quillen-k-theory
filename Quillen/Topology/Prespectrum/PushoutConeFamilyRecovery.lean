/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.PushoutConeFamily

/-!
# Recovery of chosen families from their original pushout-cone cells

Restrict a jointly continuous based prespectrum family to its Laurent, polynomial, and
overlap cells. Descending these restrictions recovers the entire original family, not
merely its endpoints or homotopy class. This retains previously chosen fillers when
restricting a higher-dimensional parameter family to its boundary.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Quillen.LoopPrespectrum.PushoutConeFamily

variable {T : Type v} [TopologicalSpace T]
variable {A B C L Y : LoopPrespectrum.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {c : HomotopyPushout.prespectrum f g ⟶ L}
variable (k : (n : ℕ) → C(T × (mappingCone c).space n, Y.space n))
  (hp : ∀ n t, k n (t, (mappingCone c).point n) = Y.point n)
  (hs : ∀ n t x z, k (n + 1) (t, (mappingCone c).structureMap n x z) =
    Y.structureMap n (k n (t, x)) z)

/-- Restrict an actual family to all four original types of cells, with their full parameters. -/
def ofFamily : PushoutConeFamily T f g c Y where
  laurent n := ⟨fun z ↦ k n (z.1, (mappingConeInclusion c).map n z.2), by fun_prop⟩
  plus n := ⟨fun z ↦ k n (z.1, (mappingConeHomotopy c).level n
    (z.2.1, (HomotopyPushout.inl f g).map n z.2.2)), by fun_prop⟩
  minus n := ⟨fun z ↦ k n (z.1, (mappingConeHomotopy c).level n
    (z.2.1, (HomotopyPushout.inr f g).map n z.2.2)), by fun_prop⟩
  overlap n := ⟨fun z ↦ k n (z.1, (mappingConeHomotopy c).level n
    (z.2.1, HomotopyPushout.cylinder f g n z.2.2)), by fun_prop⟩
  overlap_zero n t h x := by
    change k n (t, (mappingConeHomotopy c).level n
      (h, HomotopyPushout.cylinder f g n (0, x))) = _
    rw [HomotopyPushout.cylinder_zero]
    rfl
  overlap_one n t h x := by
    change k n (t, (mappingConeHomotopy c).level n
      (h, HomotopyPushout.cylinder f g n (1, x))) = _
    rw [HomotopyPushout.cylinder_one]
    rfl
  overlap_base n t h s := by
    change k n (t, (mappingConeHomotopy c).level n
      (h, HomotopyPushout.cylinder f g n (s, A.point n))) = _
    rw [HomotopyPushout.cylinder_point]
    rfl
  plus_zero n t x := congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_zero n ((HomotopyPushout.inl f g).map n x))
  minus_zero n t x := congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_zero n ((HomotopyPushout.inr f g).map n x))
  overlap_height_zero n t s x := congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_zero n (HomotopyPushout.cylinder f g n (s, x)))
  plus_one n t x := (congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_one n ((HomotopyPushout.inl f g).map n x))).trans (hp n t)
  minus_one n t x := (congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_one n ((HomotopyPushout.inr f g).map n x))).trans (hp n t)
  overlap_height_one n t s x := (congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_one n (HomotopyPushout.cylinder f g n (s, x)))).trans (hp n t)
  laurent_point n t := hp n t
  plus_point n t h := (congrArg (fun x ↦ k n (t, x))
    ((mappingConeHomotopy c).at_point n h)).trans (hp n t)
  laurent_structure n t x z := hs n t ((mappingConeInclusion c).map n x) z
  plus_structure n t h x z := hs n t ((mappingConeHomotopy c).level n
    (h, (HomotopyPushout.inl f g).map n x)) z
  minus_structure n t h x z := hs n t ((mappingConeHomotopy c).level n
    (h, (HomotopyPushout.inr f g).map n x)) z
  overlap_structure n t h s x z := hs n t ((mappingConeHomotopy c).level n
    (h, HomotopyPushout.cylinder f g n (s, x))) z

variable [LocallyCompactSpace T]

/-- Descending the cell restrictions preserves every point of the chosen original family. -/
theorem ofFamily_desc (n : ℕ) (t : T) (x : (mappingCone c).space n) :
    (ofFamily k hp hs).desc n (t, x) = k n (t, x) := by
  induction x using Quot.inductionOn with
  | h x => cases x with
    | inl x => rfl
    | inr x =>
      rcases x with ⟨h, x⟩
      induction x using Quot.inductionOn with
      | h x => cases x with
        | inl x => cases x <;> rfl
        | inr x => rfl

/-- Restricting a previously chosen filler to any parameter face retains that whole filler. -/
theorem ofFamily_desc_restrict {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
    (q : C(S, T)) (n : ℕ) (t : S) (x : (mappingCone c).space n) :
    ((ofFamily k hp hs).restrict q).desc n (t, x) = k n (q t, x) :=
  ((ofFamily k hp hs).desc_restrict q n t x).trans (ofFamily_desc k hp hs n (q t) x)

/-- Parameter looping retains the same chosen filler at each independent loop coordinate. -/
theorem ofFamily_looped (n : ℕ) (t : T)
    (x : (parameterLooping (mappingCone c)).space n) (s : unitInterval) :
    Path.toContinuousMap ((ofFamily k hp hs).looped n (t, x)) s =
      k n (t, Path.toContinuousMap x s) :=
  ofFamily_desc k hp hs n t (Path.toContinuousMap x s)

/-- Restrict a fixed chosen coherent homotopy to its complete original double-quotient cells. -/
def ofHomotopy {l r : mappingCone c ⟶ Y} (H : Homotopy l r) :
    PushoutConeFamily unitInterval f g c Y := ofFamily H.level H.at_point H.comm

/-- The entire chosen homotopy is recovered with its original time coordinate. -/
theorem ofHomotopy_desc {l r : mappingCone c ⟶ Y} (H : Homotopy l r)
    (n : ℕ) (t : unitInterval) (x : (mappingCone c).space n) :
    (ofHomotopy H).desc n (t, x) = H.level n (t, x) :=
  ofFamily_desc H.level H.at_point H.comm n t x

end Quillen.LoopPrespectrum.PushoutConeFamily
