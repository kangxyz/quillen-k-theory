/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Aglib.CategoryTheory.ExactCategory.Basic
import Quillen.Aglib.CategoryTheory.ExactCategory.BaseChangeSquare

open CategoryTheory.ExactCategory


/-!
# Constructing admissible kernels in given pullback squares

A consumer starts with an arbitrary pullback square and obtains an admissible
kernel map by lifting the original kernel and the zero map into that square.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Quillen
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) {S : ShortComplex C}

example (hS : E.conflation S) {P T : C}
    {k : P ⟶ S.X₂} {q : P ⟶ T} {f : T ⟶ S.X₃}
    (sq : IsPullback k q S.g f) :
    E.inflation (sq.lift S.f 0 (by simp only [S.zero, zero_comp])) := by
  exact E.inflation_of_conflation (E.conflation_of_isPullback hS sq
    (sq.lift S.f 0 (by simp only [S.zero, zero_comp]))
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _))
