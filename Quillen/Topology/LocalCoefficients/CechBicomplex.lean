/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CechBisimplicial
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# The actual twisted Čech bicomplex and its augmentation

Taking alternating faces in the two genuine simplicial directions constructs
the bicomplex. Its augmentation is a genuine bicomplex morphism whose every
row map is proved a quasi-isomorphism by the explicit extra degeneracy.
We also construct the original total map; no total quasi-isomorphism or
spectral-sequence convergence is assumed here.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type u}
  (U : ι → Set X) (A : System.{u, u} X)

/-- The actual Čech row complexes vary simplicially in singular degree. -/
def cechSimplicialRowComplexes : SimplicialObject (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  cechBisimplicialModule U A ⋙ AlgebraicTopology.alternatingFaceMapComplex _

/-- The target rows are the original small-chain modules in Čech degree zero. -/
def smallSimplicialSingleRows : SimplicialObject (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  smallSimplicialModule U A ⋙ ChainComplex.single₀ _

/-- The original row augmentations form a natural transformation. -/
def cechSimplicialRowAugmentation :
    cechSimplicialRowComplexes U A ⟶ smallSimplicialSingleRows U A where
  app n := cechRowAugmentation U A n.unop
  naturality _ _ α :=
    AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality (cechAugmentedRowMap U A α.unop)

/-- The actual first-quadrant bicomplex of labeled twisted singular chains. -/
def cechBicomplex : HomologicalComplex₂ (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (cechSimplicialRowComplexes U A)

/-- Original small singular chains, concentrated in Čech degree zero. -/
def smallSingleBicomplex : HomologicalComplex₂ (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (smallSimplicialSingleRows U A)

/-- The actual bicomplex augmentation induced by forgetting containing-cover labels. -/
def cechBicomplexAugmentation : cechBicomplex U A ⟶ smallSingleBicomplex U A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (cechSimplicialRowAugmentation U A)

@[simp]
theorem cechBicomplex_X (n : ℕ) : (cechBicomplex U A).X n = cechRowComplex U A ⦋n⦌ := rfl

@[simp]
theorem cechBicomplexAugmentation_f (n : ℕ) :
    (cechBicomplexAugmentation U A).f n = cechRowAugmentation U A ⦋n⦌ := rfl

/-- Every original augmented row map is a quasi-isomorphism, without covering assumptions. -/
theorem cechBicomplexAugmentation_row_quasiIso (n : ℕ) :
    QuasiIso ((cechBicomplexAugmentation U A).f n) :=
  cechRowAugmentation_quasiIso U A ⦋n⦌

/-- The genuine total complex, including the standard total-differential signs. -/
def cechTotalComplex : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (cechBicomplex U A).total (ComplexShape.down ℕ)

/-- The genuine total target concentrated in Čech degree zero. -/
def smallSingleTotalComplex : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (smallSingleBicomplex U A).total (ComplexShape.down ℕ)

/-- Totalization of the original bicomplex augmentation. -/
def cechTotalAugmentation : cechTotalComplex U A ⟶ smallSingleTotalComplex U A :=
  HomologicalComplex₂.total.map (cechBicomplexAugmentation U A) (ComplexShape.down ℕ)

/-- The actual total differential squares to zero. -/
@[reassoc]
theorem cechTotalComplex_d_squared (n : ℕ) :
    (cechTotalComplex U A).d (n + 2) (n + 1) ≫
      (cechTotalComplex U A).d (n + 1) n = 0 :=
  (cechTotalComplex U A).d_comp_d _ _ _

end Quillen.LocalCoefficients
