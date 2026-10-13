/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SimplexProductMaps

/-! Regression tests for arbitrary local systems and the original first-vertex maps. -/

@[expose] public section
noncomputable section
open CategoryTheory Convexity Quillen.LocalCoefficients
universe u
variable (X : Type u) [TopologicalSpace X]

example (n : ℕ) (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) :
    pullback (simplexProductProjection X n) (pullback (simplexProductVertex X n 0) A) ≅ A :=
  simplexProductVertexCoefficients X n 0 A

example (n : ℕ) (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1))))
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    (simplexProductVertexCoefficients X n 0 A).hom.app (FundamentalGroupoid.mk z) =
      simplexTransport A (simplexProductSlice X n z.1) (StdSimplex.single 0) z.2 :=
  simplexProductVertexCoefficients_hom_app_eq_simplexTransport X n 0 A z

example (n k : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) :
    pushforwardHomologyMap (simplexProductVertex X n 0) A k =
      coefficientHomologyMap (simplexProductVertexChangeCoefficients X n 0 v A).hom k ≫
        pushforwardHomologyMap (simplexProductVertex X n v) A k :=
  simplexProductVertex_homology_change X n 0 v A k

example {Y : Type u} [TopologicalSpace Y] (m n k : ℕ) (f : C(X, Y))
    (g : C(X × StdSimplex ℝ (Fin (m + 1)), Y × StdSimplex ℝ (Fin (n + 1))))
    (h : (simplexProductProjection Y n).comp g = f.comp (simplexProductProjection X m))
    (A : System.{u, u} (Y × StdSimplex ℝ (Fin (n + 1)))) :
    IsIso (pushforwardHomologyMap g A k) ↔
      IsIso (pushforwardHomologyMap f (pullback (simplexProductVertex Y n 0) A) k) :=
  simplexProductMap_homology_isIso_iff m n f g h A k
