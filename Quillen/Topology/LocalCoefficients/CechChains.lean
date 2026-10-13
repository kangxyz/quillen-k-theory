/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SmallChains
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Actual Čech rows of twisted small singular chains

In a fixed singular degree, a Čech simplex records an original small singular
simplex and an ordered nonempty list of cover members containing its entire
image. Its coefficient is the original local-system fiber at the first vertex.
Forgetting cover labels gives the original small-chain module.
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

/-- The actual members of a cover containing the whole given singular simplex. -/
abbrev CechLabel (U : ι → Set X) {n : SimplexCategory}
    (σ : CoverSmallSimplex U n) := {i : ι // Set.range σ.val ⊆ U i}

/-- One genuine containing cover member, chosen separately for each small simplex. -/
def chooseCechLabel (U : ι → Set X) {n : SimplexCategory}
    (σ : CoverSmallSimplex U n) : CechLabel U σ :=
  ⟨σ.property.choose, σ.property.choose_spec⟩

/-- Actual singular simplices together with ordered containing-cover labels. -/
abbrev CechSimplex (U : ι → Set X) (n p : SimplexCategory) :=
  Σ σ : CoverSmallSimplex U n, Fin (p.len + 1) → CechLabel U σ

/-- Restriction acts only on the list of cover labels. -/
def restrictCechSimplex (U : ι → Set X) (n : SimplexCategory)
    {p q : SimplexCategory} (t : CechSimplex U n q) (α : p ⟶ q) : CechSimplex U n p :=
  ⟨t.1, fun i ↦ t.2 (α.toOrderHom i)⟩

/-- The actual local-system coefficient module in one Čech and singular bidegree. -/
def cechChainModule (U : ι → Set X) (A : System.{u, u} X) (n p : SimplexCategory) :
    ModuleCat.{u} ℤ :=
  ∐ fun t : CechSimplex U n p ↦ simplexFiber A t.1.val

/-- The original coefficient summand of a labeled singular simplex. -/
def cechChainInclusion (U : ι → Set X) (A : System.{u, u} X) {n p : SimplexCategory}
    (t : CechSimplex U n p) : simplexFiber A t.1.val ⟶ cechChainModule U A n p :=
  Sigma.ι (fun s : CechSimplex U n p ↦ simplexFiber A s.1.val) t

/-- Čech restriction leaves the singular simplex and every coefficient unchanged. -/
def cechChainMap (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory)
    {p q : SimplexCategory} (α : p ⟶ q) :
    cechChainModule U A n q ⟶ cechChainModule U A n p :=
  Sigma.desc fun t ↦ cechChainInclusion U A (restrictCechSimplex U n t α)

/-- The genuine simplicial module in the cover direction at fixed singular degree. -/
def cechSimplicialModule (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory) :
    SimplicialObject (ModuleCat.{u} ℤ) where
  obj p := cechChainModule U A n p.unop
  map α := cechChainMap U A n α.unop
  map_id p := by
    apply Sigma.hom_ext
    intro t
    simp [cechChainMap, cechChainInclusion, restrictCechSimplex, cechChainModule]
  map_comp α β := by
    apply Sigma.hom_ext
    intro t
    simp [cechChainMap, cechChainInclusion, restrictCechSimplex, SimplexCategory.comp_toOrderHom]

/-- Forgetting all cover labels retains the original small singular chain. -/
def cechModuleAugmentation (U : ι → Set X) (A : System.{u, u} X) (n p : SimplexCategory) :
    cechChainModule U A n p ⟶ smallChainModule U A n :=
  Sigma.desc fun t ↦ smallChainInclusion U A t.1

/-- The actual augmented Čech row of local-coefficient chains. -/
def cechAugmentedRow (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory) :
    SimplicialObject.Augmented (ModuleCat.{u} ℤ) where
  left := cechSimplicialModule U A n
  right := smallChainModule U A n
  hom :=
    { app p := cechModuleAugmentation U A n p.unop
      naturality _ _ α := by
        apply Sigma.hom_ext
        intro t
        simp [cechSimplicialModule, cechChainMap, cechModuleAugmentation,
          cechChainInclusion, restrictCechSimplex] }

/-- The degree-zero section chooses one actual containing cover member. -/
def cechAugmentationSection (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory) :
    smallChainModule U A n ⟶ cechChainModule U A n ⦋0⦌ :=
  Sigma.desc fun σ ↦ cechChainInclusion U A ⟨σ, fun _ ↦ chooseCechLabel U σ⟩

/-- Insert the chosen containing member at the beginning of the actual label list. -/
def cechExtraDegeneracyMap (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory)
    (p : ℕ) : cechChainModule U A n ⦋p⦌ ⟶ cechChainModule U A n ⦋p + 1⦌ :=
  Sigma.desc fun t ↦ cechChainInclusion U A ⟨t.1, Fin.cons (chooseCechLabel U t.1) t.2⟩

end Quillen.LocalCoefficients
