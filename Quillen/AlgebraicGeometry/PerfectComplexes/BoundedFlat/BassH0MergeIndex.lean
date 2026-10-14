/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassSupportOrder

/-! Explicit representatives of the already checked 63-slot scalar support arrangement. -/
@[expose] public section
set_option autoImplicit false
namespace Quillen.PerfectComplexes.BassH0Merged

/-- The finite ordered support representatives retain every original slot. -/
def select (i : Fin 63) : Fin 45 ⊕ Fin 31 :=
  if h₀ : i.val < 2 then .inr ⟨i.val, by omega⟩ else
  if h₁ : i.val < 6 then .inr ⟨i.val + 2, by omega⟩ else
  if h₂ : i.val < 10 then .inr ⟨i.val + 9, by omega⟩ else
  if h₃ : i.val < 16 then .inr ⟨i.val + 15, by omega⟩ else
  if h₄ : i.val < 20 then .inl ⟨i.val - 1, by omega⟩ else
  if h₅ : i.val = 20 then .inr 8 else
  if h₆ : i.val < 36 then .inl ⟨i.val - 21, by omega⟩ else
  if h₇ : i.val < 41 then .inl ⟨i.val - 17, by omega⟩ else
  if h₈ : i.val = 41 then .inl 39 else
  if h₉ : i.val = 42 then .inr 19 else
  if h₁₀ : i.val < 58 then .inl ⟨i.val - 19, by omega⟩ else
    .inl ⟨i.val - 18, by omega⟩

/-- Thirteen scalar coincidences select old representatives; other H0 slots stay separate. -/
def h0Representative (i : Fin 31) : Fin 45 ⊕ Fin 31 :=
  match i.val with
  | 2 => .inl 15
  | 3 => .inl 18
  | 9 => .inl 0
  | 10 => .inl 14
  | 11 => .inl 21
  | 12 => .inl 1
  | 13 => .inl 2
  | 14 => .inl 39
  | 20 => .inl 24
  | 21 => .inl 38
  | 22 => .inl 42
  | 23 => .inl 25
  | 24 => .inl 26
  | _ => .inr i

theorem select_old (i : Fin 45) : select (BassSupportOrder.oldIndex i) = .inl i := by
  fin_cases i <;> rfl

theorem select_h0 (i : Fin 31) :
    select (BassSupportOrder.h0Index i) = h0Representative i := by
  fin_cases i <;> rfl

end Quillen.PerfectComplexes.BassH0Merged
