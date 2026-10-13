/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.LocalCoefficients.CoveringNaturality

/-!
# Consumers of the actual regular covering-chain comparison

QuillenTest exercise the monodromy-selected lift, the first face, arbitrary
restrictions, the genuine differential, both inverse identities, and the
original-map square. They retain arbitrary covering spaces and do not
assume that fundamental groups are commutative.
-/

open CategoryTheory Convexity Quillen Quillen.LocalCoefficients
open scoped Simplicial

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p) [SimplyConnectedSpace E] (e₀ : E)

-- A regular basis path selects exactly its actual lifted endpoint.
example {n : SimplexCategory} (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp e₀ n s (StdSimplex.single 0) =
      (hp.monodromy s.2 ⟨e₀, rfl⟩).1 := by
  rw [coveringRegularSimplexEquiv_apply, Covering.lift_vertex]

-- Every regular generator maps to the corresponding actual lifted simplex.
example {n : SimplexCategory} (s : RegularSimplex (p e₀) n) (z : ℤ) :
    (coveringModuleIso hp e₀ n).inv
      (integralChainGenerator (coveringRegularSimplexEquiv hp e₀ n s) z) =
        regularChainGenerator (p e₀) s z := by
  rw [← coveringModuleIso_generator]
  exact ModuleCat.inv_hom_apply _ _

-- In particular, the face beginning at vertex one is respected with its monodromy.
example (s : RegularSimplex (p e₀) ⦋2⦌) (z : ℤ) :
    (coveringModuleIso hp e₀ ⦋1⦌).hom
        (chainMap (regular (p e₀)) (SimplexCategory.δ 0)
          (regularChainGenerator (p e₀) s z)) =
      integralChainGenerator
        (restrictSimplex (coveringRegularSimplexEquiv hp e₀ ⦋2⦌ s)
          (SimplexCategory.δ 0)) z := by
  simp [coveringRegularSimplexEquiv_restrict]

-- The all-operator theorem includes degeneracies in every degree.
example {n : ℕ} (s : RegularSimplex (p e₀) ⦋n⦌) (i : Fin (n + 1)) (z : ℤ) :
    (coveringModuleIso hp e₀ ⦋n + 1⦌).hom
        (chainMap (regular (p e₀)) (SimplexCategory.σ i)
          (regularChainGenerator (p e₀) s z)) =
      integralChainGenerator
        (restrictSimplex (coveringRegularSimplexEquiv hp e₀ ⦋n⦌ s)
          (SimplexCategory.σ i)) z := by
  simp [coveringRegularSimplexEquiv_restrict]

-- The equality is of the original differentials, not only induced homology maps.
example (n : ℕ) :
    (singularChainComplex (regular (p e₀))).d (n + 1) n ≫
        (coveringModuleIso hp e₀ ⦋n⦌).hom =
      (coveringModuleIso hp e₀ ⦋n + 1⦌).hom ≫
        (singularChainComplex (constant E integralCoefficients)).d (n + 1) n :=
  coveringModuleIso_d hp e₀ (n + 1) n

-- This is the actual mathlib singular chain complex with the explicitly lifted integers.
example :
    (coveringChainIso hp e₀).inv ≫ (coveringChainIso hp e₀).hom =
      𝟙 (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).obj (TopCat.of E)) :=
  (coveringChainIso hp e₀).inv_hom_id

-- Base fundamental groups remain potentially noncommutative; the action is left regular.
example (g r : FundamentalGroup B (p e₀)) (z : ℤ) :
    (regularMonodromy (p e₀) g).asHom (regularSingle (p e₀) r z) =
      regularSingle (p e₀) (r ≫ g) z :=
  regularMonodromy_single (p e₀) g r z

-- Neither of the horizontal maps is assumed to be a covering map or an equivalence.
example {E' B' : Type u} [TopologicalSpace E'] [TopologicalSpace B']
    [SimplyConnectedSpace E'] {p' : E' → B'} (hp' : IsCoveringMap p')
    (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e)) :
    regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringConstantChainIso hp' (k e₀)).hom =
      (coveringConstantChainIso hp e₀).hom ≫
        pushforwardChainMap k (constant E' integralCoefficients) :=
  coveringConstantChainIso_map hp hp' k f h e₀

-- The same square lands in mathlib's singularChainComplexFunctor with its literal map of k.
example {E' B' : Type u} [TopologicalSpace E'] [TopologicalSpace B']
    [SimplyConnectedSpace E'] {p' : E' → B'} (hp' : IsCoveringMap p')
    (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e)) :
    regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringChainIso hp' (k e₀)).hom =
      (coveringChainIso hp e₀).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
          integralCoefficients).map (TopCat.ofHom k) :=
  coveringChainIso_map hp hp' k f h e₀
