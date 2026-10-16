/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Homology.TotalComplex.RowContraction

/-! # Consumers of the genuine first-quadrant row-contraction comparison -/

@[expose] public section

open CategoryTheory

universe u

example {K : HomologicalComplex₂ (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {C : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ HomologicalComplex₂.single₀Bicomplex C)
    (s : ∀ i, (HomologicalComplex₂.single₀Bicomplex C).X i ⟶ K.X i)
    (hs : ∀ i, s i ≫ f.f i = 𝟙 _)
    (h : ∀ i, Homotopy (𝟙 (K.X i)) (f.f i ≫ s i)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) :=
  Quillen.HomologicalAlgebra.total_quasiIso_of_row_contractions f s hs h

example {K : HomologicalComplex₂ (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {C : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ HomologicalComplex₂.single₀Bicomplex C)
    (s : ∀ i, (HomologicalComplex₂.single₀Bicomplex C).X i ⟶ K.X i)
    (hs : ∀ i, s i ≫ f.f i = 𝟙 _)
    (h : ∀ i, Homotopy (𝟙 (K.X i)) (f.f i ≫ s i)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) n) := by
  let := Quillen.HomologicalAlgebra.total_quasiIso_of_row_contractions f s hs h
  infer_instance
