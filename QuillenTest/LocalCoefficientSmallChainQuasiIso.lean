/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SmallChainQuasiIso
public import QuillenTest.LocalCoefficientSmallChains

/-!
# Consumers of the actual open-cover small-chain quasi-isomorphism

These tests retain regular path-class coefficient transport, arbitrary open
covers, and the proper two-interval cover crossed by an explicit original
singular simplex. The comparison is always the original small-chain inclusion.
-/

@[expose] public section

open Quillen.LocalCoefficients


noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v

namespace QuillenTest.LocalCoefficientSmallChainQuasiIso

open Quillen

open LocalCoefficients LocalCoefficientChains LocalCoefficientSmallChains

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The theorem applies to regular path-class coefficients with arbitrary
monodromy, in every degree and for every open cover. -/
example (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (b : X) (V : ModuleCat.{u} ℤ) :
    QuasiIso (smallChainComplexInclusion U (regularSystem b V)) :=
  smallChainComplexInclusion_quasiIso U hU hcover (regularSystem b V)

/-- Both actual operators restrict even to a family that is not an open cover. -/
example (U : ι → Set X) (A : System.{u, u} X) :
    Homotopy (𝟙 (smallChainComplex U A)) (smallBarycentricSubdivision U A) :=
  smallBarycentricSubdivisionHomotopy U A

/-- A common finite depth works for any genuine finite chain, including a sum
of coefficients on different singular simplices. -/
example (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (A : System.{u, u} X) (n : ℕ)
    (x y : (singularChainComplex A).X n) :
    ∃ k : ℕ, ∀ m, k ≤ m →
      (barycentricSubdivisionIterate A m).f n (x + y) ∈ smallChainSubmodule U A n :=
  exists_eventually_barycentricSubdivisionIterate_mem U hU hcover A n (x + y)

/-- The comparison is an isomorphism even though the original crossing simplex
is not small for either of the two proper members of the cover. -/
theorem proper_cover_comparison (V : ModuleCat.{0} ℤ) :
    (¬ IsCoverSmall intervalCover crossingSimplex) ∧
      QuasiIso (smallChainComplexInclusion intervalCover (regularSystem (0 : ℝ) V)) :=
  ⟨crossingSimplex_not_small,
    smallChainComplexInclusion_quasiIso intervalCover intervalCover_open
      intervalCover_covers (regularSystem (0 : ℝ) V)⟩

/-- Every coefficient on the explicit crossing segment becomes small after
actual iterated subdivision, with its path-class coefficients preserved. -/
example (V : ModuleCat.{0} ℤ)
    (a : simplexFiber (regularSystem (0 : ℝ) V) crossingSimplex) :
    ∃ k : ℕ, ∀ m, k ≤ m →
      (barycentricSubdivisionIterate (regularSystem (0 : ℝ) V) m).f 1
        (chainInclusion (regularSystem (0 : ℝ) V) crossingSimplex a) ∈
          smallChainSubmodule intervalCover (regularSystem (0 : ℝ) V) 1 :=
  exists_eventually_barycentricSubdivisionIterate_mem intervalCover intervalCover_open
    intervalCover_covers _ _ _

/-- The homology isomorphism has exactly the original inclusion-induced map. -/
example (V : ModuleCat.{0} ℤ) (n : ℕ) :
    (smallChainHomologyIso intervalCover intervalCover_open intervalCover_covers
      (regularSystem (0 : ℝ) V) n).hom =
      HomologicalComplex.homologyMap
        (smallChainComplexInclusion intervalCover (regularSystem (0 : ℝ) V)) n := rfl

/-- In particular the actual degree-zero and positive-degree homology maps
are isomorphisms, without assuming any acyclicity of the coefficients. -/
example (V : ModuleCat.{0} ℤ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (smallChainComplexInclusion intervalCover (regularSystem (0 : ℝ) V)) n) :=
  smallChainComplexInclusion_homology_isIso intervalCover intervalCover_open
    intervalCover_covers _ n

end QuillenTest.LocalCoefficientSmallChainQuasiIso
