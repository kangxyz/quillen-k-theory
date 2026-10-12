/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Stable general linear groups over arbitrary rings

The finite stages are units of square matrices. Stabilization adjoins a final
identity entry, and the stable group is their directed limit. No commutativity,
nontriviality, or invariant basis number assumption is used.

The canonical `of` maps are injective and admit bundled compatible `lift`s.
Finite families admit a common finite-stage representative. `transition_val_fromBlocks`
identifies arbitrary transitions with block diagonal extension, and `map` supplies
functorial entrywise change of coefficients for unital ring homomorphisms.

These are algebraic foundations for the usual stable general linear group in
Quillen's plus construction; this file does not construct the plus construction
or identify its higher homotopy groups.
-/
@[expose] public section

universe u

namespace Quillen.StableGeneralLinear

variable (R : Type u) [Ring R]

/-- The finite general linear group, including rank zero. -/
abbrev GL (n : ℕ) := (Matrix (Fin n) (Fin n) R)ˣ

/-- Adjoin a one-dimensional identity block before reindexing. -/
def blockStep (n : ℕ) : GL R n →* (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  toFun g :=
    { val := Matrix.fromBlocks g.val 0 0 1
      inv := Matrix.fromBlocks g.inv 0 0 1
      val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
      inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one] }
  map_one' := by apply Units.ext; exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Units.ext
    simp [Matrix.fromBlocks_multiply]

/-- The usual stabilization `g ↦ diag(g,1)` in the standard finite indexing. -/
def step (n : ℕ) : GL R n →* GL R (n + 1) :=
  (Units.map (Matrix.reindexRingEquiv R finSumFinEquiv).toMonoidHom).comp (blockStep R n)

@[simp] lemma step_val_castSucc (n : ℕ) (g : GL R n) (i j : Fin n) :
    (step R n g).val i.castSucc j.castSucc = g.val i j := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm j.castSucc) = _
  simp

@[simp] lemma step_val_last (n : ℕ) (g : GL R n) :
    (step R n g).val (Fin.last n) (Fin.last n) = 1 := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm (Fin.last n)) (finSumFinEquiv.symm (Fin.last n)) = _
  simp

@[simp] lemma step_val_castSucc_last (n : ℕ) (g : GL R n) (i : Fin n) :
    (step R n g).val i.castSucc (Fin.last n) = 0 := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm (Fin.last n)) = _
  simp

@[simp] lemma step_val_last_castSucc (n : ℕ) (g : GL R n) (j : Fin n) :
    (step R n g).val (Fin.last n) j.castSucc = 0 := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm (Fin.last n)) (finSumFinEquiv.symm j.castSucc) = _
  simp

lemma step_injective (n : ℕ) : Function.Injective (step R n) := by
  intro g h e
  apply Units.ext
  have e' := congrArg (fun a : GL R (n + 1) =>
    a.val.submatrix (fun i => finSumFinEquiv (Sum.inl i))
      (fun i => finSumFinEquiv (Sum.inl i))) e
  ext i j
  have e'' := congrFun (congrFun e' i) j
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) =
    Matrix.fromBlocks h.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) at e''
  simpa only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁] using e''


/-- The transition map from rank `n` to rank `m`. -/
def transition (n m : ℕ) (h : n ≤ m) : GL R n →* GL R m where
  toFun := Nat.leRecOn h (fun {k} => step R k)
  map_one' := by
    induction h using Nat.leRec with
    | refl => exact Nat.leRecOn_self _
    | @le_succ_of_le m h ih => rw [Nat.leRecOn_succ h, ih, map_one]
  map_mul' g k := by
    induction h using Nat.leRec with
    | refl => simp only [Nat.leRecOn_self]
    | @le_succ_of_le m h ih => simp only [Nat.leRecOn_succ h, ih, map_mul]

@[simp] lemma transition_self (n : ℕ) (g : GL R n) : transition R n n le_rfl g = g :=
  Nat.leRecOn_self g

lemma transition_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (g : GL R n) :
    transition R m k h' (transition R n m h g) = transition R n k (h.trans h') g :=
  (Nat.leRecOn_trans h h' g).symm

@[simp] lemma transition_succ (n : ℕ) (g : GL R n) :
    transition R n (n + 1) (Nat.le_succ n) g = step R n g := Nat.leRecOn_succ' g

lemma transition_step {n m : ℕ} (h : n ≤ m) (g : GL R n) :
    transition R n (m + 1) (Nat.le_succ_of_le h) g = step R m (transition R n m h g) :=
  Nat.leRecOn_succ h g

/-- Stabilization leaves all original matrix entries unchanged. -/
@[simp] lemma transition_val_castLE {n m : ℕ} (h : n ≤ m) (g : GL R n)
    (i j : Fin n) :
    (transition R n m h g).val (i.castLE h) (j.castLE h) = g.val i j := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g]
    change (step R m (transition R n m h g)).val
      (i.castLE h).castSucc (j.castLE h).castSucc = _
    rw [step_val_castSucc, ih]

/-- Every row beyond the original rank is the corresponding identity row. -/
lemma transition_val_of_le_left {n m : ℕ} (h : n ≤ m) (g : GL R n)
    (i j : Fin m) (hi : n ≤ i.val) :
    (transition R n m h g).val i j = (1 : Matrix (Fin m) (Fin m) R) i j := by
  induction h using Nat.leRec with
  | refl => exact False.elim (Nat.not_le_of_gt i.isLt hi)
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g]
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp_all [Matrix.one_apply, eq_comm]

/-- Every column beyond the original rank is the corresponding identity column. -/
lemma transition_val_of_le_right {n m : ℕ} (h : n ≤ m) (g : GL R n)
    (i j : Fin m) (hj : n ≤ j.val) :
    (transition R n m h g).val i j = (1 : Matrix (Fin m) (Fin m) R) i j := by
  induction h using Nat.leRec with
  | refl => exact False.elim (Nat.not_le_of_gt j.isLt hj)
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g]
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp_all [Matrix.one_apply, eq_comm]

/-- Arbitrary stabilization is a block diagonal extension by an identity matrix. -/
lemma transition_val_fromBlocks (n m : ℕ) (g : GL R n) :
    (transition R n (n + m) (Nat.le_add_right n m) g).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin m) (Fin m) R)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact transition_val_castLE R _ g i j
    | inr j =>
      rw [transition_val_of_le_right R _ g _ _ (Nat.le_add_right n j.val)]
      simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
      simp
  | inr i =>
    rw [transition_val_of_le_left R _ g _ _ (Nat.le_add_right n i.val)]
    cases j <;> simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq] <;> simp [Matrix.one_apply]

instance : DirectedSystem (GL R) (fun n m h => transition R n m h) where
  map_self := fun {_} => transition_self R _
  map_map := fun {_ _ _} => transition_trans R

lemma transition_injective (n m : ℕ) (h : n ≤ m) :
    Function.Injective (transition R n m h) := by
  induction h using Nat.leRec with
  | refl => intro g k e; simpa using e
  | @le_succ_of_le m h ih =>
    intro g k e
    apply ih
    apply step_injective R m
    simpa only [transition, MonoidHom.coe_mk, OneHom.coe_mk, Nat.leRecOn_succ h] using e

/-- The stable general linear group, formed as a genuine directed limit. -/
abbrev Group := DirectLimit (GL R) (transition R)

noncomputable section

/-- The canonical homomorphism from a finite stage. -/
def of (n : ℕ) : GL R n →* Group R where
  toFun g := ⟦⟨n, g⟩⟧
  map_one' := (DirectLimit.one_def n).symm
  map_mul' _ _ := (DirectLimit.mul_def ..).symm

@[simp] lemma of_transition {n m : ℕ} (h : n ≤ m) (g : GL R n) :
    of R m (transition R n m h g) = of R n g := DirectLimit.mk_apply ..

/-- Equality in the stable group is equality at a common finite stage. -/
lemma of_eq_iff {n m : ℕ} (g : GL R n) (h : GL R m) :
    of R n g = of R m h ↔
      ∃ k, ∃ (hn : n ≤ k) (hm : m ≤ k), transition R n k hn g = transition R m k hm h :=
  Quotient.eq

lemma of_injective (n : ℕ) : Function.Injective (of R n) :=
  DirectLimit.mk_injective _ (transition_injective R) n

/-- Every stable matrix has a finite-stage representative. -/
lemma exists_of (g : Group R) : ∃ n, ∃ a : GL R n, g = of R n a :=
  DirectLimit.exists_eq_mk _ g

/-- Two stable matrices can always be represented at one common finite stage. -/
lemma exists_of₂ (g h : Group R) :
    ∃ n, ∃ a b : GL R n, g = of R n a ∧ h = of R n b :=
  DirectLimit.exists_eq_mk₂ _ g h

/-- Compatible finite-stage homomorphisms induce a stable homomorphism. -/
def lift {H : Type*} [_root_.Group H] (f : ∀ n, GL R n →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g)) : Group R →* H where
  toFun := DirectLimit.lift (transition R) (fun n => f n) hf
  map_one' := DirectLimit.lift_one f hf
  map_mul' := DirectLimit.lift_mul f hf

@[simp] lemma lift_of {H : Type*} [_root_.Group H] (f : ∀ n, GL R n →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g))
    (n : ℕ) (g : GL R n) : lift R f hf (of R n g) = f n g := rfl

@[simp] lemma lift_comp_of {H : Type*} [_root_.Group H] (f : ∀ n, GL R n →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g)) (n : ℕ) :
    (lift R f hf).comp (of R n) = f n := rfl

/-- Every finite family admits representatives at a single finite rank. -/
lemma exists_of_family {ι : Type*} [Finite ι] (g : ι → Group R) :
    ∃ n, ∃ a : ι → GL R n, ∀ i, g i = of R n (a i) := by
  classical
  let := Fintype.ofFinite ι
  choose n a h using fun i => exists_of R (g i)
  refine ⟨Finset.univ.sup n,
    fun i => transition R (n i) _ (Finset.le_sup (Finset.mem_univ i)) (a i), ?_⟩
  intro i
  rw [of_transition, h i]

/-- Homomorphisms out of the stable group are determined by finite stages. -/
@[ext] lemma hom_ext {H : Type*} [_root_.Group H] {f g : Group R →* H}
    (h : ∀ n a, f (of R n a) = g (of R n a)) : f = g := by
  ext x
  obtain ⟨n, a, rfl⟩ := exists_of R x
  exact h n a

/-- The compatible lift is the unique homomorphism with the prescribed finite stages. -/
lemma lift_unique {H : Type*} [_root_.Group H] (f : ∀ n, GL R n →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g))
    (φ : Group R →* H) (hφ : ∀ n, φ.comp (of R n) = f n) : φ = lift R f hf := by
  apply hom_ext
  intro n g
  exact DFunLike.congr_fun (hφ n) g

section RingMap

variable {R} {S : Type*} [Ring S] {T : Type*} [Ring T]

/-- Entrywise change of rings at a finite stage, for arbitrary rings. -/
def finiteMap (f : R →+* S) (n : ℕ) : GL R n →* GL S n :=
  Units.map (RingHom.mapMatrix f).toMonoidHom

lemma finiteMap_step (f : R →+* S) (n : ℕ) (g : GL R n) :
    finiteMap f (n + 1) (step R n g) = step S n (finiteMap f n g) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  change f (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
      (finSumFinEquiv.symm (finSumFinEquiv i))
      (finSumFinEquiv.symm (finSumFinEquiv j))) =
    Matrix.fromBlocks (g.val.map f) 0 0 (1 : Matrix (Fin 1) (Fin 1) S)
      (finSumFinEquiv.symm (finSumFinEquiv i))
      (finSumFinEquiv.symm (finSumFinEquiv j))
  simp only [Equiv.symm_apply_apply]
  cases i <;> cases j <;> simp [Matrix.one_apply]

lemma finiteMap_transition (f : R →+* S) {n m : ℕ} (h : n ≤ m) (g : GL R n) :
    finiteMap f m (transition R n m h g) = transition S n m h (finiteMap f n g) := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    change finiteMap f (m + 1) (Nat.leRecOn (C := GL R) _ (fun {k} => step R k) g) =
      Nat.leRecOn (C := GL S) _ (fun {k} => step S k) (finiteMap f n g)
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h, finiteMap_step]
    exact congrArg (step S m) ih

/-- The stable general linear group is functorial for all unital ring homomorphisms. -/
def map (f : R →+* S) : Group R →* Group S :=
  lift R (fun n => (of S n).comp (finiteMap f n)) (by
    intro n m h g
    simp only [MonoidHom.comp_apply, finiteMap_transition, of_transition])

@[simp] lemma map_of (f : R →+* S) (n : ℕ) (g : GL R n) :
    map f (of R n g) = of S n (finiteMap f n g) := rfl

@[simp] lemma map_id : map (RingHom.id R) = MonoidHom.id (Group R) := by
  apply hom_ext
  intro n g
  simp only [map_of, MonoidHom.id_apply]
  congr 1

@[simp] lemma map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  apply hom_ext
  intro n a
  simp only [map_of, MonoidHom.comp_apply]
  congr 1

/-- An injective map of coefficient rings induces an injective stable group map. -/
lemma map_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro x y h
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_of₂ R x y
  rw [map_of, map_of] at h
  have h' := of_injective S n h
  congr 1
  apply Units.ext
  ext i j
  apply hf
  exact congrFun (congrFun (congrArg (fun a : GL S n => a.val) h') i) j

end RingMap

end

end Quillen.StableGeneralLinear
